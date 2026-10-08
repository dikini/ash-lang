"""Resource-bounded Lean module builds; receipts are not integration evidence.

Linux/POSIX development tooling. A shared host lock serializes these runners;
the job limit applies within one runner. External compilers/LSPs need explicit
coordination and are also accounted for by MemAvailable admission checks.
"""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time


def sha(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def available_memory_mb():
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) // 1024
    raise RuntimeError("MemAvailable is required for safe build admission")


def external_compiler_count():
    """Count other host compilers conservatively; exclude our direct children."""
    count = 0
    for process in Path("/proc").iterdir():
        if not process.name.isdigit():
            continue
        try:
            command = (process / "comm").read_text().strip()
            if command not in {"lean", "rustc", "rust-lld", "lake"}:
                continue
            status = (process / "status").read_text()
            parent = int(re.search(r"^PPid:\s*(\d+)", status, re.M)[1])
            if parent == os.getpid() or re.search(r"^State:\s*Z", status, re.M):
                continue
            args = (process / "cmdline").read_bytes().split(b"\0")
            lightweight = {b"--version", b"-v", b"--short-version", b"--githash",
                           b"--deps", b"--src-deps", b"--print-prefix", b"--print-libdir",
                           b"--help", b"-h", b"--features"}
            if command == "lean" and lightweight & set(args):
                continue
            count += 1
        except (OSError, ProcessLookupError):
            continue  # A compiler exited during the inventory.
    return count


def validate_log(log, expected):
    output = Path(log).read_text()
    if re.search(r"\b(?:error:|warning:|sorryAx)", output):
        raise ValueError("Lean log contains an error, warning or sorryAx")
    reports = re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)", output)
    axioms = {atom.strip() for block in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
              for atom in block.split(",") if atom.strip()}
    if axioms - {"propext", "Quot.sound", "Classical.choice"}:
        raise ValueError("Lean log contains an unapproved axiom")
    if reports != expected:
        raise ValueError("Lean report names differ from the reviewed list")
    return reports


def _atomic_copy(source, destination):
    temporary = destination.with_suffix(destination.suffix + ".tmp")
    shutil.copyfile(source, temporary)
    os.replace(temporary, destination)


def _one(name, *, snapshot, cache, store, imports, reports, source_hashes,
         compiler, libraries, options, environment):
    source = snapshot / (name + ".lean")
    artifact, log = cache / (name + ".olean"), cache / (name + ".log")
    dependency_hashes = {d: sha(cache / (d + ".olean")) for d in imports[name]}
    inputs = {"schema": 1, "runner_sha256": sha(__file__), "module": name,
              "source_sha256": source_hashes[name], "compiler": str(compiler),
              "compiler_library_hashes": libraries, "options": options,
              "reports": reports[name], "direct_import_artifacts": dependency_hashes}
    key = hashlib.sha256(json.dumps(inputs, sort_keys=True).encode()).hexdigest()
    entry = store / key
    receipt = entry / "receipt.json"

    def check_inputs():
        if sha(source) != source_hashes[name]:
            raise ValueError("source changed during build")
        for dependency, digest in dependency_hashes.items():
            if sha(cache / (dependency + ".olean")) != digest:
                raise ValueError("selected import changed during build")
        # Verify the actual paths selected by Lean, including unexpected local
        # imports missed by the registration parser. Builtins use the pinned
        # compiler library; no other external project artifacts are accepted.
        dep_result = subprocess.run([str(compiler), "--deps", source.name],
                                    cwd=snapshot, env=environment,
                                    text=True, capture_output=True, check=True)
        selected = {Path(p).resolve() for p in dep_result.stdout.splitlines() if p.strip()}
        project = {p for p in selected if p.parent == cache}
        expected = {cache / (d + ".olean") for d in imports[name]}
        library_root = compiler.parent.parent / "lib/lean"
        if project != expected or any(p not in expected and not p.is_relative_to(library_root)
                                      for p in selected):
            raise ValueError("Lean selected imports outside the declared cache/library")

    check_inputs()
    try:
        saved = json.loads(receipt.read_text())
        if saved["inputs"] != inputs or saved["exit_code"] != 0:
            raise ValueError("receipt inputs mismatch")
        if sha(entry / "module.olean") != saved["artifact_sha256"]:
            raise ValueError("receipt artifact hash mismatch")
        if sha(entry / "module.log") != saved["log_sha256"]:
            raise ValueError("receipt log hash mismatch")
        validate_log(entry / "module.log", reports[name])
        _atomic_copy(entry / "module.olean", artifact)
        _atomic_copy(entry / "module.log", log)
        now = time.monotonic()
        return {**saved, "receipt": str(receipt), "cache_hit": True,
                "started_at": now, "finished_at": now, "wall_seconds": 0.0,
                "original_wall_seconds": saved["wall_seconds"], "log": str(log)}
    except (OSError, ValueError, KeyError, TypeError):
        pass  # Invalid or incomplete receipts are misses, never proof evidence.

    started = time.monotonic()
    command = [str(compiler), *options, "-o", str(artifact), source.name]
    with log.open("wb") as output:
        process = subprocess.Popen(command, cwd=snapshot, env=environment,
                                   stdout=output, stderr=subprocess.STDOUT)
        _, status, usage = os.wait4(process.pid, 0)
        process.returncode = os.waitstatus_to_exitcode(status)
    finished = time.monotonic()
    metrics = {"started_at": started, "finished_at": finished,
               "wall_seconds": finished - started, "peak_rss_kib": usage.ru_maxrss,
               "exit_code": process.returncode, "command": command,
               "origin_cwd": str(snapshot), "origin_lean_path": str(cache),
               "log": str(log), "cache_hit": False}
    if process.returncode:
        return {**metrics, "failure": "Lean compilation failed"}
    try:
        validate_log(log, reports[name])
        if not artifact.stat().st_size:
            raise ValueError("empty Lean artifact")
        check_inputs()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        return {**metrics, "failure": str(error)}

    saved = {**metrics, "inputs": inputs, "artifact_sha256": sha(artifact),
             "log_sha256": sha(log), "reports": reports[name]}
    # Publish a complete directory after artifact/log validation. The host lock
    # excludes other runner writers; interrupted temporary entries are ignored.
    temporary = Path(tempfile.mkdtemp(prefix="pending-", dir=store))
    try:
        shutil.copyfile(artifact, temporary / "module.olean")
        shutil.copyfile(log, temporary / "module.log")
        (temporary / "receipt.json").write_text(json.dumps(saved, indent=2) + "\n")
        if entry.exists():
            shutil.rmtree(entry)
        os.replace(temporary, entry)
    finally:
        if temporary.exists():
            shutil.rmtree(temporary)
    return {**saved, "receipt": str(receipt)}


def build(*, snapshot, cache, store, modules, imports, reports, source_hashes,
          compiler, libraries, jobs=1, memory_mb=4096, headroom_mb=4096,
          host_lock=None):
    """Build ready modules, retain successes on failure, and return progress."""
    if type(jobs) is not int or jobs not in (1, 2):
        raise ValueError("jobs must be 1 or 2; serial is the default")
    if type(memory_mb) is not int or memory_mb < 1 or headroom_mb < 0:
        raise ValueError("positive compiler memory and nonnegative headroom required")
    if jobs > len(os.sched_getaffinity(0)):
        raise ValueError("jobs exceeds the process CPU allocation")
    if len(modules) != len(set(modules)):
        raise ValueError("duplicate modules")
    snapshot, cache, store = (Path(p).resolve() for p in (snapshot, cache, store))
    compiler = Path(compiler).resolve()
    if str(compiler) not in libraries:
        raise ValueError("compiler hash pin is required")
    if not all(re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", n) for n in modules):
        raise ValueError("invalid module name")
    options = ["-DwarningAsError=true", "-j1", f"-M{memory_mb}"]
    environment = dict(os.environ, LEAN_PATH=str(cache),
                       PATH=str(compiler.parent) + ":" + os.environ["PATH"])
    lock_path = Path(host_lock) if host_lock else Path.home() / ".cache/ash/lean-build.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    store.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    records, failures, blocked, running = {}, {}, [], {}
    pending = list(modules)
    max_running = 0
    resource_blocked = False
    other_compilers_at_start = external_compiler_count()

    def pinned_libraries():
        for path, digest in libraries.items():
            if sha(path) != digest:
                raise ValueError("compiler/library hash pin changed: " + path)

    with lock_path.open("a") as lock:
        # Do not wait behind an unseen heavy build. The caller can retry later.
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return {"status": "resource_blocked", "reason": "another runner holds the host lock",
                    "records": {}, "failures": {}, "blocked": [], "pending": pending,
                    "max_running": 0, "wall_seconds": time.monotonic() - started}
        pinned_libraries()
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            while pending or running:
                while True:
                    newly_blocked = [n for n in pending if any(
                        d in failures or d in blocked for d in imports[n])]
                    if not newly_blocked:
                        break
                    blocked.extend(newly_blocked)
                    pending = [n for n in pending if n not in newly_blocked]
                for name in list(pending):
                    if len(running) >= jobs:
                        break
                    if any(d in modules and d not in records for d in imports[name]):
                        continue
                    if available_memory_mb() < headroom_mb + (len(running) + 1) * memory_mb:
                        continue
                    if external_compiler_count() + len(running) >= 2:
                        continue
                    pending.remove(name)
                    future = pool.submit(_one, name, snapshot=snapshot, cache=cache,
                                         store=store, imports=imports, reports=reports,
                                         source_hashes=source_hashes, compiler=compiler,
                                         libraries=libraries, options=options, environment=environment)
                    running[future] = name
                    max_running = max(max_running, len(running))
                if not running:
                    if pending:
                        ready = [n for n in pending if all(d not in modules or d in records
                                                          for d in imports[n])]
                        if not ready:
                            raise ValueError("cyclic or unresolved module dependencies")
                        resource_blocked = True
                    break
                completed, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in completed:
                    name = running.pop(future)
                    try:
                        record = future.result()
                    except Exception as error:
                        record = {"failure": str(error)}
                    (failures if "failure" in record else records)[name] = record
                    print(json.dumps({"module": name, "status": "failed" if "failure" in record
                                      else "cached" if record["cache_hit"] else "compiled",
                                      "wall_seconds": record.get("wall_seconds"),
                                      "peak_rss_kib": record.get("peak_rss_kib")}), flush=True)
        try:
            pinned_libraries()
        except ValueError:
            # No success compiled under drifting library pins may be reused.
            for record in records.values():
                if not record["cache_hit"]:
                    shutil.rmtree(Path(record["receipt"]).parent)
            raise
    return {"status": "failed" if failures else "resource_blocked" if resource_blocked else "complete",
            "records": records, "failures": failures, "blocked": blocked, "pending": pending,
            "max_running": max_running, "jobs": jobs, "memory_mb": memory_mb,
            "headroom_mb": headroom_mb, "compiler_threads": 1,
            "other_compilers_at_start": other_compilers_at_start,
            "host_compiler_launch_limit": 2,
            "wall_seconds": time.monotonic() - started}
