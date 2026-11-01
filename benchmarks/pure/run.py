#!/usr/bin/env python3
"""Compare fresh-process Ash, generated-host and Python resource usage on Linux."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import random
import signal
import statistics
import subprocess
import sys
import tempfile
import threading
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CASES = {
    "factorial": str(math.factorial(400)),
    "fibonacci": "17711",
    "map_fold": str(400 * 401 * 801 // 6 + 3 * 400 * 401 // 2 + 7 * 400),
    "boolean_map_fold": "false",
}
CASE_TYPES = {"boolean_map_fold": "Bool"}
METRICS = ("wall_seconds", "user_seconds", "system_seconds", "cpu_seconds", "peak_rss_kib")
TIME = Path("/usr/bin/time")


def measure(argv, timeout):
    """Use wait4 CPU and GNU time RSS, excluding the runner's pre-exec RSS."""
    expired = threading.Event()
    with (tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr,
          tempfile.TemporaryDirectory(prefix="ash-benchmark-") as temporary):
        rss_path = Path(temporary) / "rss.txt"
        measured_argv = [TIME, "-f", "%M", "-o", rss_path, "--", *argv]
        start = time.perf_counter_ns()
        process = subprocess.Popen(
            measured_argv, cwd=ROOT, stdout=stdout, stderr=stderr, start_new_session=True,
        )

        def kill():
            expired.set()
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

        timer = threading.Timer(timeout, kill)
        timer.start()
        try:
            _, status, usage = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(status)
        except BaseException:
            kill()
            _, status, _ = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(status)
            raise
        finally:
            stop = time.perf_counter_ns()
            timer.cancel()
            timer.join()
        stdout.seek(0)
        stderr.seek(0)
        # GNU time forks from its small native image. Using the outer Python
        # child's ru_maxrss would include this runner's inherited pre-exec RSS.
        rss_lines = rss_path.read_text().splitlines() if rss_path.exists() else []
        rss = int(rss_lines[-1]) if rss_lines and rss_lines[-1].isdigit() else None
        if not expired.is_set() and rss is None:
            raise RuntimeError("GNU time did not report peak RSS")
        return {
            "argv": [str(arg) for arg in argv],
            "monitor_argv": [str(arg) for arg in measured_argv],
            "wall_seconds": (stop - start) / 1e9,
            "user_seconds": usage.ru_utime,
            "system_seconds": usage.ru_stime,
            "cpu_seconds": usage.ru_utime + usage.ru_stime,
            "peak_rss_kib": rss,
            "exit_code": process.returncode,
            "timed_out": expired.is_set(),
            "stdout": stdout.read().decode("utf-8", errors="replace"),
            "stderr": stderr.read().decode("utf-8", errors="replace"),
        }


def require_success(sample, expected=None):
    if sample["timed_out"] or sample["exit_code"] != 0:
        raise RuntimeError(
            f"command failed (status {sample['exit_code']}, timeout={sample['timed_out']}): "
            f"{sample['argv']}\n{sample['stderr']}"
        )
    if expected is not None and sample["stdout"].strip() != expected:
        raise RuntimeError(f"wrong result from {sample['argv']}: {sample['stdout']!r}")


def summarize(samples):
    return {
        metric: {
            "median": statistics.median(sample[metric] for sample in samples),
            "min": min(sample[metric] for sample in samples),
            "max": max(sample[metric] for sample in samples),
        }
        for metric in METRICS
    }


def fingerprint(paths):
    result = {}
    for path in sorted(set(paths)):
        with path.open("rb") as stream:
            result[str(path)] = hashlib.file_digest(stream, "sha256").hexdigest()
    return result


def positive_int(value):
    number = int(value)
    if number <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def nonnegative_int(value):
    number = int(value)
    if number < 0:
        raise argparse.ArgumentTypeError("must be nonnegative")
    return number


def positive_float(value):
    number = float(value)
    if not math.isfinite(number) or number <= 0:
        raise argparse.ArgumentTypeError("must be finite and positive")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ash", type=Path, default=ROOT / "target/release/ash")
    parser.add_argument("--repeats", type=positive_int, default=5)
    parser.add_argument("--build-repeats", type=positive_int, default=1)
    parser.add_argument("--warmups", type=nonnegative_int, default=1)
    parser.add_argument("--timeout", type=positive_float, default=120)
    parser.add_argument("--build-timeout", type=positive_float, default=1200)
    parser.add_argument("--case", choices=CASES, action="append")
    parser.add_argument("--cargo-target-dir", type=Path, default=ROOT / "target")
    parser.add_argument("--compiler-source-root", type=Path, default=ROOT,
                        help="matching compiler checkout to fingerprint when building hosts")
    parser.add_argument("--reuse-builds", type=Path,
                        help="reuse pinned hosts and successful build samples from an earlier receipt")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if sys.platform != "linux":
        parser.error("Linux is required for RSS in KiB and the generated-host target")
    if not TIME.is_file():
        parser.error("GNU /usr/bin/time is required for target-only peak RSS")
    ash = args.ash.resolve()
    if not ash.is_file() or not os.access(ash, os.X_OK):
        parser.error(f"build the Ash executable first; missing executable: {ash}")
    output = (args.output or ROOT / "target/pure-benchmark" / str(time.time_ns())).resolve()
    output.mkdir(parents=True, exist_ok=False)
    cache = args.cargo_target_dir.resolve()
    compiler_root = args.compiler_source_root.resolve()
    cases = list(dict.fromkeys(args.case or CASES))
    prior = None
    build_origin = None
    receipt_chain = []
    hosts = {case: output / f"{case}-host" for case in cases}
    if args.reuse_builds:
        prior = json.loads(args.reuse_builds.read_text())
        if prior.get("inputs_before") != prior.get("inputs_after"):
            parser.error("reused builds require an unchanged original input snapshot")
        build_origin = prior
        while build_origin.get("reused_build_receipt"):
            origin_path = Path(build_origin["reused_build_receipt"]).resolve()
            if origin_path in receipt_chain:
                parser.error("cyclic build receipt chain")
            receipt_chain.append(origin_path)
            build_origin = json.loads(origin_path.read_text())
        if build_origin.get("inputs_before") != build_origin.get("inputs_after"):
            parser.error("original build inputs changed during measurement")
        for case in cases:
            if case not in prior["cases"]:
                parser.error(f"no recorded build for {case}; select recorded cases or build afresh")
        for path in [ash, *(HERE / f"{case}.{suffix}" for case in cases for suffix in ("ash", "py"))]:
            if fingerprint([path])[str(path)] != prior["inputs_before"].get(str(path)):
                parser.error(f"reused build input changed: {path}")
        for case in cases:
            entry = prior["cases"][case]
            if not entry["build"]:
                parser.error(f"no successful build samples for {case}")
            for sample in entry["build"]:
                require_success(sample)
            argv = entry["build"][-1]["argv"]
            hosts[case] = Path(argv[argv.index("--output") + 1])
            if fingerprint([hosts[case]])[str(hosts[case])] != entry["host_sha256"]:
                parser.error(f"reused host changed: {hosts[case]}")

    def input_paths():
        used = [ash, TIME, Path(sys.executable).resolve(), *HERE.glob("*.py"), *HERE.glob("*.ash")]
        if prior is not None:
            return [*used, args.reuse_builds.resolve(), *receipt_chain, *hosts.values()]
        return [*used, compiler_root / "Cargo.toml", compiler_root / "Cargo.lock",
                compiler_root / "rust-toolchain.toml", compiler_root / "build.rs",
                *compiler_root.glob("locales/*.ftl"), *compiler_root.glob(".cargo/*.toml"),
                *(path for path in compiler_root.glob("src/**/*") if path.is_file())]
    report = {
        "schema_version": 1,
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "python": sys.version,
        "git_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "git_status": subprocess.check_output(["git", "status", "--short"], cwd=ROOT, text=True),
        "rustc": subprocess.check_output(["rustc", "--version"], cwd=ROOT, text=True).strip(),
        "cpu_model": next((line.split(":", 1)[1].strip() for line in
                           Path("/proc/cpuinfo").read_text().splitlines()
                           if line.startswith("model name")), "unknown"),
        "cpu_affinity": sorted(os.sched_getaffinity(0)),
        "settings": {"repeats": args.repeats, "build_repeats": args.build_repeats,
                     "warmups": args.warmups, "timeout": args.timeout,
                     "build_timeout": args.build_timeout, "cache": str(cache),
                     "compiler_source_root": str(compiler_root), "order_seed": 0},
        "reused_build_receipt": str(args.reuse_builds.resolve()) if prior is not None else None,
        "build_inputs": build_origin["inputs_before"] if prior is not None else None,
        "reused_build_metadata": (
            {
                "git_head": build_origin["git_head"], "git_status": build_origin["git_status"],
                "build_environment": build_origin["build_environment"], "setup": build_origin["setup"],
            }
        ) if prior is not None else None,
        "build_environment": {key: os.environ.get(key) for key in (
            "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER", "RUSTUP_TOOLCHAIN",
            "CARGO_BUILD_TARGET", "CARGO_PROFILE_RELEASE_OPT_LEVEL",
            "CARGO_PROFILE_RELEASE_DEBUG", "CARGO_PROFILE_RELEASE_LTO",
        )},
        "inputs_before": fingerprint(input_paths()),
        "setup": [],
        "cases": {},
        "complete": False,
    }

    def build(source, destination):
        previous = set((output / ".ash-build").glob("*/native-build.log"))
        sample = measure([ash, "build", "--output", destination,
                          "--cargo-target-dir", cache, source], args.build_timeout)
        current = set((output / ".ash-build").glob("*/native-build.log"))
        sample["generated_build_logs"] = [str(path) for path in sorted(current - previous)]
        sample["generated_manifests"] = {
            str(path.parent / "Cargo.toml"): (path.parent / "Cargo.toml").read_text()
            for path in sorted(current - previous)
        }
        return sample

    try:
        # Warm native dependencies once, retaining and reporting this setup cost.
        # Each measured build still generates and links a fresh root package.
        if prior is None:
            warm_source = output / "warmup.ash"
            warm_source.write_text("main : Unit -> Int\nmain () = 0\n")
            print("Preparing shared host build cache...", flush=True)
            setup = build(warm_source, output / "warmup-host")
            report["setup"].append(setup)
            require_success(setup)

        for case in cases:
            print(f"{'Reusing' if prior is not None else 'Building'} {case}...", flush=True)
            entry = {"expected": CASES[case], "expected_type": CASE_TYPES.get(case, "Int"),
                     "build": [], "warmups": [],
                     "runs": {lane: [] for lane in ("ash_run", "ash_host", "python")}}
            report["cases"][case] = entry
            host = hosts[case]
            if prior is not None:
                entry["build"] = prior["cases"][case]["build"]
            else:
                for _ in range(args.build_repeats):
                    sample = build(HERE / f"{case}.ash", host)
                    entry["build"].append(sample)
                    require_success(sample)
            entry["host_sha256"] = fingerprint([host])[str(host)]

        rng = random.Random(0)
        print("Running and checking outputs...", flush=True)
        for case, entry in report["cases"].items():
            lanes = {
                "ash_run": ([ash, HERE / f"{case}.ash"],
                            f"{CASES[case]} : {CASE_TYPES.get(case, 'Int')}"),
                "ash_host": ([hosts[case]], CASES[case]),
                "python": ([sys.executable, "-I", "-B", HERE / f"{case}.py"], CASES[case]),
            }
            for round_index in range(args.warmups + args.repeats):
                order = list(lanes)
                rng.shuffle(order)
                for lane in order:
                    argv, expected = lanes[lane]
                    sample = measure(argv, args.timeout)
                    sample["lane"] = lane
                    sample["round"] = round_index
                    bucket = entry["warmups"] if round_index < args.warmups else entry["runs"][lane]
                    bucket.append(sample)
                    require_success(sample, expected)
            entry["summary"] = {lane: summarize(samples) for lane, samples in entry["runs"].items()}
            entry["summary"]["build"] = summarize(entry["build"])
        report["inputs_after"] = fingerprint(input_paths())
        if report["inputs_before"] != report["inputs_after"]:
            raise RuntimeError("benchmark inputs changed during measurement")
        report["complete"] = True
    except (OSError, RuntimeError) as error:
        report["error"] = str(error)
        raise
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        (output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"Receipt: {output / 'results.json'}", flush=True)

    print("\nMedians; build and run are separate. CPU = user + system. RSS = peak resident memory.")
    print(f"{'case':<18} {'lane':<10} {'wall ms':>12} {'CPU ms':>12} {'RSS MiB':>12}")
    for case, entry in report["cases"].items():
        for lane in ("build", "ash_run", "ash_host", "python"):
            summary = entry["summary"][lane]
            print(f"{case:<18} {lane:<10} {summary['wall_seconds']['median'] * 1000:12.3f} "
                  f"{summary['cpu_seconds']['median'] * 1000:12.3f} "
                  f"{summary['peak_rss_kib']['median'] / 1024:12.3f}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError) as error:
        sys.exit(str(error))
