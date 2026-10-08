#!/usr/bin/env python3
"""Bounded fresh-process Ash/Rust reference measurements, without Cargo.

Generate inputs with resource_reference_cases.py generate --output INPUTS
--cli RELEASE_ASH --rustc PINNED_RUSTC. Then run:
  resource_reference_measurements.py run INPUTS/reference-manifest.json
      --output NEW_RESULTS --protocol FROZEN_PROTOCOL.json

Rust metadata compilation is an explicitly measured frontend reference. Its
work does not equal Ash's checking, Core validation and evaluation pipeline.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
import tempfile
import threading
import time

sys.dont_write_bytecode = True
import resource_calibration as collector


WINDOW_SECONDS = 180
PROCESS_SECONDS = 10
WARMUPS = 1
REPETITIONS = 3
CURVES = {
    "nested_type": {"source-checking": [15, 272, 386],
                    "independent-effect-core": [28, 269, 451]},
    "prerequisite": {"source-checking": [25, 346, 2165],
                     "independent-effect-core": [157, 623, 1752, 2]},
}
METRICS = ("wrapper_wall_seconds", "wrapper_child_user_seconds",
           "wrapper_child_system_seconds", "wrapper_child_total_seconds",
           "target_wall_seconds", "target_user_seconds", "target_system_seconds",
           "target_peak_rss_kib")


def resolved(path, base):
    path = Path(path)
    return (path if path.is_absolute() else base / path).resolve()


def predict(family, depth, phase):
    coefficients = CURVES.get(family, {}).get(phase)
    if coefficients is None:
        return None
    a, b, c = coefficients[:3]
    numerator = a * depth * depth + b * depth + c
    denominator = coefficients[3] if len(coefficients) == 4 else 1
    return numerator // denominator if numerator % denominator == 0 else numerator / denominator


def sample(spec, argv, output, label, deadline, limit, *, observed=False,
           output_artifact=None, timed=True):
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise TimeoutError("global 180-second measurement window expired")
    directory = output / label
    directory.mkdir(parents=True, exist_ok=False)
    stdout, stderr, timing = (directory / name for name in ("stdout.log", "stderr.log", "time.json"))
    cwd = Path(spec["cwd"]).resolve()
    inputs = collector.snapshot(spec.get("input_paths", []), cwd)
    issues = []
    if any("error" in item for item in inputs):
        issues.append("immutable input missing")
    input_hashes = {item["path"]: item.get("sha256") for item in inputs}
    for path, expected in spec.get("input_sha256", {}).items():
        if input_hashes.get(str(resolved(path, cwd))) != expected:
            issues.append(f"pinned input differs: {path}")
    executable = resolved(argv[0], cwd)
    executable_before = collector.sha(executable) if executable.is_file() else None
    if executable_before is None:
        issues.append("executable missing")
    artifact = resolved(output_artifact, cwd) if output_artifact else None
    if artifact:
        if str(artifact) in input_hashes:
            raise ValueError("output artifact overlaps immutable source")
        artifact.unlink(missing_ok=True)
    environment = os.environ.copy()
    environment["ASH_CALIBRATION_OBSERVE"] = "1" if observed else "0"
    environment["ASH_CALIBRATION_LIMIT"] = str(limit)
    command = ["/usr/bin/time", "-f", collector.TIME_FORMAT, "-o", str(timing), "--", *argv]
    fired = threading.Event()
    started_utc = collector.utc_now()
    exit_code, spawn_error, watchdog = None, None, None
    with stdout.open("wb") as out, stderr.open("wb") as err:
        cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
        wall_start = time.monotonic_ns()
        try:
            process = subprocess.Popen(command, cwd=cwd, env=environment, stdout=out,
                                       stderr=err, start_new_session=True)

            def terminate():
                fired.set()
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass

            watchdog = threading.Timer(min(PROCESS_SECONDS, max(0.001, deadline - time.monotonic())), terminate)
            watchdog.daemon = True
            watchdog.start()
            # Blocking wait avoids subprocess.wait(timeout)'s polling latency.
            exit_code = process.wait()
        except OSError as error:
            spawn_error = str(error)
        finally:
            wall_end = time.monotonic_ns()
            cpu_after = resource.getrusage(resource.RUSAGE_CHILDREN)
            if watchdog:
                watchdog.cancel()
                watchdog.join()
    target = collector.external_time(timing)
    cpu = {"before": {"user_seconds": cpu_before.ru_utime, "system_seconds": cpu_before.ru_stime},
           "after": {"user_seconds": cpu_after.ru_utime, "system_seconds": cpu_after.ru_stime},
           "user_seconds": cpu_after.ru_utime - cpu_before.ru_utime,
           "system_seconds": cpu_after.ru_stime - cpu_before.ru_stime,
           "units": "native-precision CPU seconds, unrounded",
           "ownership": "GNU time wrapper plus reaped target descendants; excludes Python runner"}
    cpu["total_seconds"] = cpu["user_seconds"] + cpu["system_seconds"]
    metrics = {"wrapper_wall_seconds": (wall_end - wall_start) / 1_000_000_000,
               "wrapper_child_user_seconds": cpu["user_seconds"],
               "wrapper_child_system_seconds": cpu["system_seconds"],
               "wrapper_child_total_seconds": cpu["total_seconds"]}
    if target:
        metrics.update({"target_" + key: target.get(key) for key in
                        ("wall_seconds", "user_seconds", "system_seconds", "peak_rss_kib")})
    else:
        issues.append("missing GNU time target metrics")
    if fired.is_set():
        issues.append("process group killed at external deadline")
    if spawn_error:
        issues.append(f"spawn failed: {spawn_error}")
    if exit_code != spec.get("expected_exit", 0):
        issues.append(f"exit {exit_code}, expected {spec.get('expected_exit', 0)}")
    if stdout.read_text(errors="replace").strip() != spec.get("expected_stdout", "").strip():
        issues.append("unexpected stdout")
    after_inputs = collector.snapshot(spec.get("input_paths", []), cwd)
    executable_after = collector.sha(executable) if executable.is_file() else None
    if after_inputs != inputs or executable_after != executable_before:
        issues.append("input or executable changed during process")
    artifact_record = None
    if artifact:
        artifact_record = {"path": str(artifact), "exists": artifact.is_file()}
        if artifact.is_file():
            artifact_record.update({"bytes": artifact.stat().st_size, "sha256": collector.sha(artifact)})
        if not artifact.is_file() or not artifact.stat().st_size:
            issues.append("required output artifact absent or empty")
    observation = collector.records_from_logs(stdout, stderr, observed,
                                              collector.PHASES if observed else [])
    issues.extend(observation["errors"])
    record = {"label": label, "timed": timed, "observed": observed,
              "started_utc": started_utc, "argv": argv, "cwd": str(cwd),
              "executable_sha256": executable_before, "executable_sha256_after": executable_after,
              "inputs": inputs, "inputs_after": after_inputs, "output_artifact": artifact_record,
              "exit_code": exit_code, "timed_out": fired.is_set(), "spawn_error": spawn_error,
              "diagnostic_limit": limit, "wrapper_wall_ns": wall_end - wall_start,
              "wrapper_inclusive_child_cpu": cpu, "gnu_time": target, "metrics": metrics,
              "stdout": {"path": str(stdout), "sha256": collector.sha(stdout)},
              "stderr": {"path": str(stderr), "sha256": collector.sha(stderr)},
              "time_file": {"path": str(timing), "sha256": collector.sha(timing) if timing.exists() else None},
              "observation": observation, "issues": issues, "valid": not issues}
    collector.dump(directory / "result.json", record)
    return record


def load_manifest(path):
    manifest = json.loads(path.read_text())
    pairs = manifest.get("pairs", [])
    if len(pairs) != 14:
        raise ValueError("reference protocol requires exactly 14 pairs")
    ids = [pair["id"] for pair in pairs]
    if len(set(ids)) != 14 or any(not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", name) for name in ids):
        raise ValueError("pair ids must be unique safe filenames")
    if manifest["harness"]["asserted_case_ids"] != ids:
        raise ValueError("native validation harness must assert all 14 paired cases in order")
    ash_executables = {pair["ash"]["argv"][0] for pair in pairs}
    rust_executables = {pair["rust"]["argv"][0] for pair in pairs}
    if len(ash_executables) != 1 or len(rust_executables) != 1:
        raise ValueError("each language must reuse one pinned executable")
    for pair in pairs:
        rust = pair["rust"]
        if Path(rust["argv"][0]).name != "rustc" or "--emit=metadata" not in rust["argv"]:
            raise ValueError("Rust reference must use direct rustc --emit=metadata")
        if any("incremental" in argument for argument in rust["argv"]):
            raise ValueError("incremental Rust compilation is outside the fixed protocol")
        if pair.get("held_out", False) != (pair["parameters"].get("depth") in (24, 32)):
            raise ValueError("depths 24/32 must be explicitly marked held out")
        if not rust.get("metadata_output"):
            raise ValueError("Rust metadata output path missing")
    harness = manifest["harness"]
    if harness["compile_argv"][0] not in rust_executables:
        raise ValueError("native harness must use the same pinned Rust compiler")
    harness_source = resolved(harness["entry_path"], Path(harness["cwd"])).read_text()
    assertions = re.findall(r'assert_eq!\(case(\d+)::run\(\),\s*42,\s*"([^"\n]+)"\);', harness_source)
    if assertions != [(str(index), name) for index, name in enumerate(ids)]:
        raise ValueError("native harness source must contain exactly the 14 generated run()==42 assertions")
    return manifest


def report(manifest, records, protocol, output, interrupted=None):
    cases = []
    for pair in manifest["pairs"]:
        own = [record for record in records if record.get("case") == pair["id"]]
        item = {"id": pair["id"], "family": pair["family"], "parameters": pair["parameters"],
                "held_out": pair.get("held_out", False), "startup_control": pair.get("startup_control", False),
                "shared_structure": pair["shared_structure"], "differences": pair["differences"],
                "language_metrics": {}, "charge_predictions": {}, "issues": []}
        for language in ("ash", "rust"):
            measured = [record for record in own if record.get("language") == language and
                        record.get("kind") == "measured"]
            good = [record for record in measured if record["valid"]]
            item["language_metrics"][language] = {key: collector.summarize(record["metrics"].get(key) for record in good)
                                                  for key in METRICS}
            if len(measured) != REPETITIONS or len(good) != REPETITIONS:
                item["issues"].append(f"{language}: incomplete/failed three-run timing set")
        observer = [record for record in own if record.get("kind") == "observer"]
        if len(observer) == 1 and observer[0]["valid"]:
            observed = observer[0]["observation"]
            item["ash_work"] = observed["work"]
            item["ash_phases"] = observed["phases"]
            item["ash_input"] = observed["input"]
            for phase in ("source-checking", "independent-effect-core"):
                expected = predict(pair["family"], pair["parameters"].get("depth", 0), phase)
                if expected is not None:
                    actual = observed["work"][phase]["work_cumulative"]
                    item["charge_predictions"][phase] = {"predicted": expected, "actual": actual,
                                                         "residual": actual - expected, "exact_match": actual == expected}
        else:
            item["issues"].append("missing or failed Ash observer process; no completed work inferred")
        item["issues"].extend(issue for record in own for issue in record["issues"])
        item["controlled_complete"] = not item["issues"]
        for key in METRICS:
            a, r = item["language_metrics"]["ash"][key], item["language_metrics"]["rust"][key]
            item.setdefault("ash_to_rust_median_ratios", {})[key] = a["median"] / r["median"] if a and r and r["median"] else None
        cases.append(item)
    result = {"created_utc": collector.utc_now(), "frozen_protocol": protocol,
              "interrupted": interrupted, "cases": cases, "raw_process_count": len(records),
              "complete": not interrupted and all(case["controlled_complete"] for case in cases) and
                          all(record["valid"] for record in records),
              "limitations": ["Pairs match named semantic structures, not compiler work or pipeline stages.",
                              "Budget means the frozen typical charged-cost prediction; work means observed charged cost. The diagnostic refusal limit is a separate finite ceiling.",
                              "Ash timings include checking, independent Core validation and evaluation; Rust metadata emission includes its own analyses and encoding.",
                              "Rust structural work counters are unavailable; none are estimated from CPU time.",
                              "GNU time target CPU/peak RSS and high-precision wrapper-inclusive child CPU/wall are distinct measurements.",
                              "RUSAGE_CHILDREN includes GNU time and waited-for target descendants, excludes Python runner CPU; timeout orphan accounting may be incomplete.",
                              "Wall is monotonic elapsed seconds, CPU is scheduled processor seconds; native precision is platform dependent, values are not decimal-rounded.",
                              "Wrapper wall and child CPU share the same process interval; compiler threads may consume more aggregate CPU seconds than elapsed seconds.",
                              "The width-zero startup control is reported raw; no noisy subtraction of CPU/RSS is treated as measured semantic work.",
                              "All four charge curves were frozen before dispatch; there is no fitting or coefficient update.",
                              "Depths 24/32 are held-out extrapolations; prediction misses remain visible."]}
    collector.dump(output / "summary.json", result)
    lines = ["# Ash/Rust frontend reference", "", "Paired semantic structures; distinct compiler boundaries. No optimization or allowance change.", "",
             "| Pair | Held out | Ash child CPU median s | Rust child CPU median s | Ash/Rust peak RSS KiB | Source predicted/actual | Core predicted/actual |",
             "| --- | --- | ---: | ---: | --- | --- | --- |"]
    for case in cases:
        metrics = case["language_metrics"]
        def median(language, key):
            value = metrics[language][key]
            return str(value["median"]) if value else "missing"
        predictions = case["charge_predictions"]
        def prediction(phase):
            value = predictions.get(phase)
            return f"{value['predicted']} / {value['actual']}" if value else "n/a"
        lines.append(f"| {case['id']} | {case['held_out']} | {median('ash', 'wrapper_child_total_seconds')} | "
                     f"{median('rust', 'wrapper_child_total_seconds')} | {median('ash', 'target_peak_rss_kib')} / "
                     f"{median('rust', 'target_peak_rss_kib')} | {prediction('source-checking')} | {prediction('independent-effect-core')} |")
    lines.extend(["", "Median/min/max for both CPU measurements, wall and peak RSS, all six Ash ledgers, phase endpoints, source hashes, failures and raw logs are retained in JSON.", "",
                  *[f"- {limitation}" for limitation in result["limitations"]], ""])
    if interrupted:
        lines.extend([f"Window stopped: {interrupted}", ""])
    (output / "report.md").write_text("\n".join(lines))
    return result


def run(options):
    path, output = options.manifest.resolve(), options.output.resolve()
    manifest = load_manifest(path)
    supplied_protocol = json.loads(options.protocol.read_text())
    expected_curves = {"nested_type": {"source": [15, 272, 386], "core": [28, 269, 451]},
                       "prerequisite": {"source": [25, 346, 2165],
                                        "core": {"numerator": [157, 623, 1752], "denominator": 2}}}
    if supplied_protocol.get("charge_curves") != expected_curves or supplied_protocol.get("held_out_depths") != [24, 32]:
        raise ValueError("supplied frozen protocol does not match the four approved curves/held-out depths")
    if supplied_protocol.get("bounds", {}).get("diagnostic_base_limit") != options.limit:
        raise ValueError("diagnostic allowance differs from the supplied frozen protocol")
    output.mkdir(parents=True, exist_ok=False)
    protocol = {"supplied": supplied_protocol, "supplied_path": str(options.protocol.resolve()),
                "supplied_sha256": collector.sha(options.protocol), "charge_curves": CURVES,
                "window_seconds": WINDOW_SECONDS, "process_seconds": PROCESS_SECONDS,
                "actual_window_seconds": options.window_seconds,
                "warmups": WARMUPS, "repetitions": REPETITIONS, "ash_observers_per_case": 1,
                "held_out_depths": [24, 32], "diagnostic_limit": options.limit,
                "manifest_sha256": collector.sha(path), "manifest": manifest,
                "runner_sha256": collector.sha(__file__), "collector_sha256": collector.sha(collector.__file__),
                "created_utc": collector.utc_now()}
    collector.dump(output / "frozen-protocol.json", protocol)
    records, interrupted = [], None
    deadline = time.monotonic() + options.window_seconds
    with (output / "runs.jsonl").open("a") as stream:
        def dispatch(spec, argv, label, labels=None, **kwargs):
            record = sample(spec, argv, output, label, deadline, options.limit, **kwargs)
            record.update(labels or {})
            records.append(record)
            stream.write(json.dumps(record, sort_keys=True) + "\n")
            stream.flush()
            collector.dump(output / label / "result.json", record)
            print(f"{label}: {'valid' if record['valid'] else '; '.join(record['issues'])}", flush=True)
            return record
        try:
            harness = manifest["harness"]
            built = dispatch(harness, harness["compile_argv"], "harness-build", timed=False,
                             output_artifact=harness["executable_output"])
            if not built["valid"]:
                raise ValueError("native validation harness build failed; no timing cases dispatched")
            checked = dispatch(harness, harness["run_argv"], "harness-run", timed=False)
            if not checked["valid"]:
                raise ValueError("native 14-result validation failed; no timing cases dispatched")
            for pair_index, pair in enumerate(manifest["pairs"]):
                for repetition in range(WARMUPS + REPETITIONS):
                    kind = "warmup" if repetition == 0 else "measured"
                    languages = ("ash", "rust") if (pair_index + repetition) % 2 == 0 else ("rust", "ash")
                    for language in languages:
                        spec = pair[language]
                        dispatch(spec, spec["argv"], f"{pair['id']}/{kind}-{repetition}-{language}",
                                 labels={"case": pair["id"], "language": language, "kind": kind, "repetition": repetition},
                                 output_artifact=spec.get("metadata_output"))
                dispatch(pair["ash"], pair["ash"]["argv"], f"{pair['id']}/observer-ash", observed=True,
                         labels={"case": pair["id"], "language": "ash", "kind": "observer", "repetition": 0})
        except (TimeoutError, ValueError) as error:
            interrupted = str(error)
    # Include dispatch labels in the durable per-process records, not just memory.
    with (output / "runs.jsonl").open("w") as stream:
        for record in records:
            stream.write(json.dumps(record, sort_keys=True) + "\n")
            collector.dump(output / record["label"] / "result.json", record)
    result = report(manifest, records, protocol, output, interrupted)
    return 0 if result["complete"] else 1


def self_check(_options):
    with tempfile.TemporaryDirectory(prefix="ash-reference-runner-") as temporary:
        base = Path(temporary)
        child = base / "child.py"
        child.write_text("import sys,time\nif sys.argv[1]=='sleep': time.sleep(10)\nprint('42 : Int')\n")
        spec = {"cwd": str(base), "input_paths": [str(child)], "input_sha256": {str(child): collector.sha(child)},
                "expected_stdout": "42 : Int", "expected_exit": 0}
        good = sample(spec, [sys.executable, str(child), "normal"], base / "results", "normal", time.monotonic() + 5, 1024)
        assert good["valid"] and good["metrics"]["wrapper_child_total_seconds"] > 0
        assert good["metrics"]["wrapper_wall_seconds"] > 0
        killed = sample(spec, [sys.executable, str(child), "sleep"], base / "results", "timeout", time.monotonic() + 0.05, 1024)
        assert killed["timed_out"] and not killed["valid"]
        assert killed["metrics"]["wrapper_wall_seconds"] < 1
        assert predict("nested_type", 24, "source-checking") == 15554
        assert predict("prerequisite", 32, "independent-effect-core") == 91228
    print("Python-only connected measurement/watchdog check passed; no Ash or Rust engines invoked.")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    command = commands.add_parser("run")
    command.add_argument("manifest", type=Path)
    command.add_argument("--output", type=Path, required=True)
    command.add_argument("--protocol", type=Path, required=True)
    command.add_argument("--limit", type=int, default=16_777_216)
    command.add_argument("--window-seconds", type=float, default=WINDOW_SECONDS,
                         help="shorten the local window to reserve time for the combined 180-second experiment")
    command.set_defaults(func=run)
    command = commands.add_parser("self-check")
    command.set_defaults(func=self_check)
    options = parser.parse_args()
    if options.command == "run" and not 0 < options.limit <= sys.maxsize:
        parser.error("finite positive host-size diagnostic allowance required")
    if options.command == "run" and (not collector.numeric(options.window_seconds) or not 0 < options.window_seconds <= WINDOW_SECONDS):
        parser.error("local window must be finite, positive, and at most 180 seconds")
    try:
        return options.func(options)
    except (OSError, ValueError, KeyError) as error:
        print(f"resource reference: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
