#!/usr/bin/env python3
"""Bounded SQLite Rust compiler reference; no Cargo, Ash runs or model fitting.

run --output NEW --rustc PINNED --protocol FROZEN.json

The protocol freezes five cases (id, entry_path, input_paths, input_sha256,
expected_stdout), rustc_sha256, expected_release, expected_llvm_version, modes,
warmups=1, repetitions=3, compiler_processes=60, runtime_executions=10, and
bounds {total_window_seconds:180, per_process_timeout_seconds:10}.
version_queries=1 adds one compiler-version query inside the same window.
Alternatively version_queries=0 uses rustc_version_receipt {path, sha256}.
Optional common_rustc_args and pinned_native_inputs [{path,sha256}] are retained.
All relative paths resolve against the protocol directory.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
import tempfile
import time

sys.dont_write_bytecode = True
import resource_reference_measurements as reference

collector = reference.collector
MODES = {
    "metadata": ["--crate-type=lib", "--emit=metadata", "-Copt-level=0"],
    "full_unoptimized": ["--crate-type=bin", "--emit=link", "-Copt-level=0"],
    "full_optimized": ["--crate-type=bin", "--emit=link", "-Copt-level=3"],
}
WARMUPS, REPETITIONS = 1, 3
WINDOW_SECONDS, PROCESS_SECONDS = 180, 10


def resolved(path, base):
    return reference.resolved(path, base)


def pins(paths, declared, base):
    paths = sorted({str(resolved(path, base)) for path in paths})
    expected = {str(resolved(path, base)): value for path, value in declared.items()}
    if set(paths) != set(expected):
        raise ValueError("every declared immutable input needs exactly one hash pin")
    snapshot = collector.snapshot(paths, base)
    if any("error" in item for item in snapshot):
        raise ValueError("a pinned immutable input is missing")
    if any(not Path(path).is_file() for path in paths):
        raise ValueError("immutable inputs must be explicit files, not directories")
    actual = {item["path"]: item["sha256"] for item in snapshot}
    if actual != expected:
        raise ValueError("a pinned immutable input differs before dispatch")
    return paths, expected


def lexical_sources(paths):
    """Lexical file statistics; fn/type regex hits are not Rust AST counts."""
    sources = []
    for path in paths:
        if Path(path).suffix != ".rs":
            continue
        content = Path(path).read_bytes()
        source = content.decode("utf-8")
        sources.append({
            "path": path, "sha256": collector.sha(path), "bytes": len(content),
            "lines": len(source.splitlines()),
            "nonblank_lines": sum(bool(line.strip()) for line in source.splitlines()),
            "lexical_function_tokens": len(re.findall(r"\bfn\s+[A-Za-z_][A-Za-z_0-9]*", source)),
            "lexical_type_declaration_tokens": len(re.findall(r"\b(?:struct|enum|union|type|trait)\s+[A-Za-z_][A-Za-z_0-9]*", source)),
        })
    keys = ("bytes", "lines", "nonblank_lines", "lexical_function_tokens", "lexical_type_declaration_tokens")
    return {"sources": sources, "totals": {key: sum(item[key] for item in sources) for key in keys},
            "interpretation": "Physical Rust source files counted once; regex tokens include possible comments/strings and are not semantic API or AST counts."}


def prepare(protocol_path, rustc, output):
    base = protocol_path.parent
    protocol = json.loads(protocol_path.read_text())
    expected = {"schema_version": 1, "modes": list(MODES), "warmups": WARMUPS,
                "repetitions": REPETITIONS, "compiler_processes": 60, "runtime_executions": 10,
                "bounds": {"total_window_seconds": WINDOW_SECONDS, "per_process_timeout_seconds": PROCESS_SECONDS}}
    if any(protocol.get(key) != value for key, value in expected.items()):
        raise ValueError("frozen protocol differs from the fixed modes/counts/180-second bounds")
    rustc = rustc.resolve()
    if rustc.name != "rustc" or not rustc.is_file() or collector.sha(rustc) != protocol["rustc_sha256"]:
        raise ValueError("--rustc must be the pinned direct compiler binary")
    if protocol.get("expected_release") != "1.97.1" or protocol.get("expected_llvm_version") != "22.1.6":
        raise ValueError("expected the pinned Rust 1.97.1 / LLVM 22.1.6 version fields")
    receipt = protocol.get("rustc_version_receipt")
    query_count = 0 if receipt else 1
    if protocol.get("version_queries") != query_count:
        raise ValueError("freeze one version query, or supply its existing receipt")
    version_record = {"expected_release": protocol["expected_release"],
                      "expected_llvm_version": protocol["expected_llvm_version"],
                      "query_argv": [str(rustc), "--version", "--verbose"] if query_count else None}
    if receipt:
        version_path = resolved(receipt["path"], base)
        if collector.sha(version_path) != receipt["sha256"]:
            raise ValueError("compiler version receipt hash differs")
        version = version_path.read_text()
        validate_version(version, protocol)
        version_record.update({"path": str(version_path), "sha256": receipt["sha256"],
                               "stdout": version, "source": "existing receipt; no new version query"})
    common = protocol.get("common_rustc_args", [])
    if not isinstance(common, list) or any(not isinstance(arg, str) for arg in common):
        raise ValueError("common_rustc_args must be strings")
    protected = ("--edition", "--crate-type", "--crate-name", "--emit", "--out-dir", "-o")
    if any(arg.startswith(protected) or arg.removeprefix("-C").startswith(("opt-level", "debuginfo", "codegen-units", "incremental")) for arg in common):
        raise ValueError("common compiler arguments may not override the frozen compilation modes")
    native = protocol.get("pinned_native_inputs", [])
    native_paths, native_pins = pins([item["path"] for item in native],
                                    {item["path"]: item["sha256"] for item in native}, base)
    cases = protocol.get("cases", [])
    ids = [case["id"] for case in cases]
    if len(cases) != 5 or len(set(ids)) != 5 or any(not re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", name) for name in ids):
        raise ValueError("exactly five uniquely named SQLite cases are required")
    prepared, all_pins = [], dict(native_pins)
    for case in cases:
        entry = str(resolved(case["entry_path"], base))
        paths, expected_pins = pins(case["input_paths"], case["input_sha256"], base)
        if entry not in paths or Path(entry).suffix != ".rs":
            raise ValueError("each Rust entry must belong to its pinned input set")
        if not isinstance(case.get("expected_stdout"), str) or not case["expected_stdout"]:
            raise ValueError("each runtime check requires a nonempty pinned stdout result")
        for path, value in expected_pins.items():
            if path in all_pins and all_pins[path] != value:
                raise ValueError("conflicting immutable source pins")
            all_pins[path] = value
        merged = {**expected_pins, **native_pins}
        prepared.append({**case, "entry_path": entry, "cwd": str(resolved(case.get("cwd", str(base)), base)),
                         "input_paths": sorted(merged), "input_sha256": merged,
                         "rust_source_statistics": lexical_sources(paths)})
    all_paths, all_pins = pins(all_pins, all_pins, base)
    plans = []
    for index, case in enumerate(prepared):
        for repetition in range(WARMUPS + REPETITIONS):
            kind = "warmup" if repetition < WARMUPS else "measured"
            # Rotate mode order, retaining one serial compiler process at a time.
            modes = list(MODES)
            shift = (index + repetition) % len(modes)
            for mode in modes[shift:] + modes[:shift]:
                suffix = ".rmeta" if mode == "metadata" else ""
                artifact = output / "artifacts" / case["id"] / f"{kind}-{repetition}-{mode}{suffix}"
                argv = [str(rustc), "--edition=2024", "--crate-name=sqlite_reference_"+case["id"].replace("-", "_"),
                        *MODES[mode], "-Cdebuginfo=0", "-Ccodegen-units=1", case["entry_path"],
                        *common, "-o", str(artifact)]
                plans.append({"case": case["id"], "mode": mode, "kind": kind, "repetition": repetition,
                              "label": f"{case['id']}/{kind}-{repetition}-{mode}", "argv": argv,
                              "output_artifact": str(artifact)})
    return {"created_utc": collector.utc_now(), "protocol_path": str(protocol_path),
            "protocol_sha256": collector.sha(protocol_path), "supplied_protocol": protocol,
            "runner_sha256": collector.sha(__file__), "sampler_sha256": collector.sha(reference.__file__),
            "collector_sha256": collector.sha(collector.__file__), "rustc_path": str(rustc),
            "rustc_sha256": collector.sha(rustc), "version": version_record,
            "cases": prepared, "all_input_paths": all_paths, "all_input_sha256": all_pins,
            "rust_source_statistics": lexical_sources(all_paths), "compile_plan": plans,
            "expected_compile_processes": 60, "expected_runtime_processes": 10,
            "expected_version_queries": query_count, "expected_target_processes": 70 + query_count}


def validate_version(stdout, protocol):
    release = protocol["expected_release"]
    fields = dict(line.split(": ", 1) for line in stdout.splitlines()[1:] if ": " in line)
    if (not stdout.startswith("rustc " + release + " ") or fields.get("release") != release
            or fields.get("LLVM version") != protocol["expected_llvm_version"]):
        raise ValueError("compiler version query differs from frozen release/LLVM fields")


def summarize(manifest, records, interrupted, output, elapsed):
    cases = []
    for case in manifest["cases"]:
        own = [row for row in records if row["case"] == case["id"]]
        result = {"id": case["id"], "rust_source_statistics": case["rust_source_statistics"], "compiler_modes": {}}
        for mode in MODES:
            measured = [row for row in own if row["mode"] == mode and row["kind"] == "measured"]
            warmup = [row for row in own if row["mode"] == mode and row["kind"] == "warmup"]
            good = [row for row in measured if row["valid"]]
            result["compiler_modes"][mode] = {
                "complete": len(good) == REPETITIONS and len(warmup) == WARMUPS and all(row["valid"] for row in warmup),
                "measured_processes": len(measured), "valid_measured_processes": len(good),
                "metrics": {key: collector.summarize(row["metrics"].get(key) for row in good) for key in reference.METRICS},
            }
        checks = [row for row in own if row["kind"] == "runtime-validation"]
        result["runtime_validation"] = {"complete": len(checks) == 2 and all(row["valid"] for row in checks),
                                         "records": [{key: row[key] for key in ("label", "mode", "valid", "issues", "executable_sha256", "stdout")} for row in checks]}
        result["issues"] = [issue for row in own for issue in row["issues"]]
        cases.append(result)
    complete = (not interrupted and len(records) == manifest["expected_target_processes"] and all(row["valid"] for row in records)
                and all(all(item["complete"] for item in case["compiler_modes"].values()) and case["runtime_validation"]["complete"] for case in cases))
    summary = {"created_utc": collector.utc_now(), "complete": complete, "interrupted": interrupted,
               "elapsed_window_seconds": elapsed, "raw_process_count": len(records),
               "compiler_process_count": sum(row["kind"] in ("warmup", "measured") for row in records),
               "version_query_process_count": sum(row["kind"] == "compiler-version" for row in records),
               "runtime_validation_process_count": sum(row["kind"] == "runtime-validation" for row in records),
               "manifest_sha256": collector.sha(output / "run-manifest.json"), "cases": cases,
               "limitations": [
                   "Five Rust SQLite counterparts; not equivalent language semantics or compiler pipelines, and not an application corpus.",
                   "Metadata emission, unoptimized native linking and optimized native linking are separate compiler boundaries.",
                   "Runtime assertion/output checks are excluded from compiler timing summaries; sampled metrics remain in raw validation records.",
                   "One warmup and three measured fresh compiler processes per case/mode; no Cargo, incremental compilation or fitted model.",
                   "Wrapper CPU includes GNU time and reaped target descendants, excludes Python; wrapper CPU and wall bracket the same interval.",
                   "GNU time target wall/CPU have centisecond formatting; RSS is process peak resident memory, not allocation bytes or live heap.",
                   "Compiler threads can consume aggregate CPU greater than wall time; failed timeout descendant CPU can be incomplete.",
                   "Only declared inputs and the direct compiler binary are pinned; host linker/sysroot/transitive system inputs are not exhaustively captured.",
                   "Lexical source counts do not measure Ash/Rust semantic AST nodes, checking obligations or equivalent runtime representations."]}
    collector.dump(output / "summary.json", summary)
    return summary


def run(options):
    started = time.monotonic()
    deadline = started + WINDOW_SECONDS
    output = options.output.resolve()
    manifest = prepare(options.protocol.resolve(), options.rustc, output)
    output.mkdir(parents=True, exist_ok=False)
    collector.dump(output / "run-manifest.json", manifest)
    original_pins = manifest["all_input_sha256"]
    cases = {case["id"]: case for case in manifest["cases"]}
    records, last_artifacts, interrupted = [], {}, None
    with (output / "runs.jsonl").open("a") as stream:
        def dispatch(case, argv, label, labels, artifact=None, timed=True, version_query=False):
            pins(manifest["all_input_paths"], original_pins, output)
            if collector.sha(manifest["rustc_path"]) != manifest["rustc_sha256"]:
                raise ValueError("compiler changed since frozen manifest")
            spec = {**case, "expected_exit": 0, "expected_stdout": "" if timed or version_query else case["expected_stdout"]}
            row = reference.sample(spec, argv, output, label, deadline, 16_777_216,
                                   output_artifact=artifact, timed=timed)
            row.update(labels)
            if version_query:
                # The shared sampler assumes exact stdout. This one information
                # query instead authenticates release/LLVM fields, retaining
                # its raw stdout/hash and all other sampler failures unchanged.
                row["sampler_issues"] = list(row["issues"])
                try:
                    validate_version(Path(row["stdout"]["path"]).read_text(), manifest["supplied_protocol"])
                except (OSError, ValueError) as error:
                    row["issues"].append(str(error))
                else:
                    row["issues"] = [issue for issue in row["issues"] if issue != "unexpected stdout"]
                row["stdout_contract"] = "frozen Rust release and LLVM version fields; raw stdout retained"
            elif Path(row["stdout"]["path"]).read_bytes() != spec["expected_stdout"].encode():
                row["issues"].append("stdout bytes differ from frozen expected output")
            try:
                pins(manifest["all_input_paths"], original_pins, output)
            except (OSError, ValueError) as error:
                row["issues"].append(str(error))
            row["valid"] = not row["issues"]
            records.append(row)
            collector.dump(output / label / "result.json", row)
            stream.write(json.dumps(row, sort_keys=True) + "\n"); stream.flush()
            print(f"{label}: {'valid' if row['valid'] else '; '.join(row['issues'])}", flush=True)
            if not row["valid"]:
                raise ValueError(f"{label} failed; further processes stopped")
            return row
        try:
            if manifest["expected_version_queries"]:
                dispatch({"cwd": str(options.protocol.resolve().parent), "input_paths": manifest["all_input_paths"],
                          "input_sha256": original_pins}, manifest["version"]["query_argv"], "compiler-version",
                         {"case": None, "mode": None, "kind": "compiler-version", "repetition": 0},
                         timed=False, version_query=True)
            for plan in manifest["compile_plan"]:
                artifact = Path(plan["output_artifact"])
                artifact.parent.mkdir(parents=True, exist_ok=True)
                row = dispatch(cases[plan["case"]], plan["argv"], plan["label"],
                               {key: plan[key] for key in ("case", "mode", "kind", "repetition")}, artifact=artifact)
                if plan["mode"] != "metadata" and plan["repetition"] == WARMUPS + REPETITIONS - 1:
                    last_artifacts[(plan["case"], plan["mode"])] = row["output_artifact"]
            for case in manifest["cases"]:
                for mode in ("full_unoptimized", "full_optimized"):
                    artifact = last_artifacts[(case["id"], mode)]
                    if collector.sha(artifact["path"]) != artifact["sha256"]:
                        raise ValueError("last compiled native artifact changed before validation")
                    runtime = {**case, "input_paths": [*case["input_paths"], artifact["path"]],
                               "input_sha256": {**case["input_sha256"], artifact["path"]: artifact["sha256"]}}
                    dispatch(runtime, [artifact["path"]], f"{case['id']}/runtime-{mode}",
                             {"case": case["id"], "mode": mode, "kind": "runtime-validation", "repetition": 0}, timed=False)
        except (TimeoutError, OSError, ValueError) as error:
            interrupted = str(error)
    summary = summarize(manifest, records, interrupted, output, time.monotonic() - started)
    return 0 if summary["complete"] else 1


def self_check():
    """Offline protocol/command census and pin rejection; launches no process."""
    with tempfile.TemporaryDirectory(prefix="sqlite-reference-protocol-") as temporary:
        base = Path(temporary)
        rustc = base / "rustc"; rustc.write_bytes(b"not executed")
        receipt = base / "version.txt"; receipt.write_text("rustc 1.97.1 (receipt)\nrelease: 1.97.1\nLLVM version: 22.1.6\n")
        bridge = base / "bridge.rs"; bridge.write_text("pub fn bridge() {}\n")
        native = base / "bridge.a"; native.write_bytes(b"pinned archive, not executed")
        cases = []
        for index in range(5):
            entry = base / f"case{index}.rs"; entry.write_text("fn main() {}\n")
            paths = [str(entry), str(bridge)]
            cases.append({"id": f"case{index}", "entry_path": str(entry), "input_paths": paths,
                          "input_sha256": {path: collector.sha(path) for path in paths}, "expected_stdout": "ok\n"})
        protocol = {"schema_version": 1, "cases": cases, "rustc_sha256": collector.sha(rustc),
                    "rustc_version_receipt": {"path": str(receipt), "sha256": collector.sha(receipt)},
                    "expected_release": "1.97.1", "expected_llvm_version": "22.1.6", "version_queries": 0,
                    "modes": list(MODES), "warmups": 1, "repetitions": 3, "compiler_processes": 60, "runtime_executions": 10,
                    "bounds": {"total_window_seconds": 180, "per_process_timeout_seconds": 10},
                    "pinned_native_inputs": [{"path": str(native), "sha256": collector.sha(native)}]}
        path = base / "protocol.json"; collector.dump(path, protocol)
        manifest = prepare(path, rustc, base / "output")
        assert len(manifest["compile_plan"]) == 60
        assert sum(plan["kind"] == "measured" for plan in manifest["compile_plan"]) == 45
        assert manifest["rust_source_statistics"]["totals"]["lexical_function_tokens"] == 6
        assert all(str(native) in case["input_paths"] for case in manifest["cases"])
        del protocol["rustc_version_receipt"]
        protocol["version_queries"] = 1
        collector.dump(path, protocol)
        queried = prepare(path, rustc, base / "output")
        assert queried["expected_target_processes"] == 71 and queried["version"]["query_argv"][-2:] == ["--version", "--verbose"]
        native.write_bytes(b"changed")
        try:
            prepare(path, rustc, base / "output")
        except ValueError:
            pass
        else:
            raise AssertionError("changed native input was accepted")
    print("Offline protocol, command census and immutable-input rejection passed; no processes launched.")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    command = commands.add_parser("run")
    command.add_argument("--output", type=Path, required=True)
    command.add_argument("--rustc", type=Path, required=True)
    command.add_argument("--protocol", type=Path, required=True)
    commands.add_parser("self-check")
    options = parser.parse_args()
    try:
        return self_check() if options.command == "self-check" else run(options)
    except (OSError, ValueError, KeyError) as error:
        print(f"SQLite Rust reference: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
