#!/usr/bin/env python3
"""Measure already-built Ash executables in fresh processes; no build commands.

Manifest: {"cases": [{"id": "flat-8", "family": "flat", "parameters":
{"width": 8}, "argv": ["/absolute/ash", "run", "fixture.ash"],
"expected_exit": 0, "input_paths": ["fixture.ash"], "held_out": false}],
"provenance": {...}, "model_features": [...], "required_phases": [...]}.
A bare case array is also accepted. Paths resolve against the manifest directory.
Only Python's standard library and GNU /usr/bin/time are required.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone


PREFIX = "ASH_CALIBRATION "
PHASES = (
    "loading", "resolution", "source-checking", "module-linking",
    "linked-interface", "final-elaboration", "independent-effect-core",
    "evaluation", "pipeline",
)
OPTIONAL_PHASES = ("input-metrics",)
LEDGERS = (
    "resolution", "source-checking", "module-linking", "linked-interface",
    "final-elaboration", "independent-effect-core",
)
MODEL_FEATURES = (
    "nodes", "type_nodes", "type_depth", "requirements", "interface_members",
    "imports", "resource_sites",
)
TIME_FORMAT = (
    '{"wall_seconds":%e,"user_seconds":%U,"system_seconds":%S,'
    '"peak_rss_kib":%M,"exit_status":%x}'
)


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def numeric(value):
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(value)


def nonnegative_integer(value):
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def summarize(values):
    values = [value for value in values if numeric(value)]
    if not values:
        return None
    return {"n": len(values), "median": statistics.median(values),
            "min": min(values), "max": max(values)}


def snapshot(paths, base):
    result = []
    for item in paths:
        path = Path(item)
        if not path.is_absolute():
            path = base / path
        path = path.resolve()
        if not path.exists():
            result.append({"path": str(path), "error": "missing"})
            continue
        children = sorted(path.rglob("*")) if path.is_dir() else [path]
        for child in children:
            if child.is_file():
                result.append({"path": str(child), "bytes": child.stat().st_size,
                               "sha256": sha(child)})
    return result


def records_from_logs(stdout, stderr, observed, required_phases):
    """Retain every record and all errors; incomplete endpoints stay absent."""
    records, errors = [], []
    for stream_name, path in (("stdout", stdout), ("stderr", stderr)):
        for number, line in enumerate(Path(path).read_text(errors="replace").splitlines(), 1):
            # Native test harnesses may prefix their first stderr line.
            position = line.find(PREFIX)
            if position < 0:
                continue
            try:
                record = json.loads(line[position + len(PREFIX):])
                if not isinstance(record, dict):
                    raise ValueError("record is not an object")
                records.append({"stream": stream_name, "line": number, "record": record})
            except (ValueError, json.JSONDecodeError) as error:
                errors.append(f"{stream_name}:{number}: invalid observer JSON: {error}")
    if not observed:
        if records:
            errors.append("observation-off control emitted observer records")
        return {"records": records, "errors": errors, "phases": {}, "work": {},
                "input": None, "complete": not errors}

    phases, work, input_records = {}, {}, []
    for entry in records:
        record = entry["record"]
        event = record.get("event")
        if event == "input":
            input_records.append(record)
            features = record.get("features")
            if not isinstance(features, dict) or not features:
                errors.append("input record has no feature vector")
            elif any(not numeric(value) or value < 0 for value in features.values()):
                errors.append("input feature values must be finite nonnegative numbers")
            continue
        phase = record.get("phase")
        if phase not in PHASES + OPTIONAL_PHASES:
            errors.append(f"unknown event/phase: {event!r}/{phase!r}")
            continue
        if event == "phase":
            needed = ("wall_ns", "rss_start_kib", "rss_end_kib", "process_peak_rss_kib")
            if any(not nonnegative_integer(record.get(key)) for key in needed):
                errors.append(f"{phase}: missing or invalid phase time/RSS fields")
            if not isinstance(record.get("completed"), bool):
                errors.append(f"{phase}: missing completion flag")
            phases.setdefault(phase, []).append(record)
            if record.get("completed") is False:
                errors.append(f"{phase}: aborted endpoint")
        elif event == "work":
            if phase not in LEDGERS:
                errors.append(f"{phase}: unexpected work owner")
            if phase in work:
                errors.append(f"{phase}: duplicate final work endpoint")
            if any(not nonnegative_integer(record.get(key)) for key in
                   ("work_cumulative", "normal_limit", "diagnostic_limit")):
                errors.append(f"{phase}: missing or invalid work fields")
            elif record["diagnostic_limit"] <= 0 or record["normal_limit"] <= 0:
                errors.append(f"{phase}: allowances must be finite positive integers")
            elif record["work_cumulative"] > record["diagnostic_limit"]:
                errors.append(f"{phase}: completed work exceeds its diagnostic allowance")
            work[phase] = record
        else:
            errors.append(f"unknown observer event: {event!r}")
    if len(input_records) != 1:
        errors.append(f"expected one immutable input record, found {len(input_records)}")
    for phase in required_phases:
        if phase not in phases:
            errors.append(f"{phase}: missing phase endpoint")
        if phase in LEDGERS and phase not in work:
            errors.append(f"{phase}: missing final work endpoint")
    phase_totals = {}
    for phase, endpoints in phases.items():
        valid = [item for item in endpoints if item.get("completed") is True]
        complete_wall = len(valid) == len(endpoints) and all(
            nonnegative_integer(item.get("wall_ns")) for item in valid)
        total = {"endpoint_count": len(endpoints), "completed_count": len(valid),
                 "wall_ns": sum(item["wall_ns"] for item in valid) if complete_wall else None,
                 "rss_boundaries": [{key: item.get(key) for key in
                                      ("rss_start_kib", "rss_end_kib", "process_peak_rss_kib")}
                                     for item in endpoints]}
        if phase in work:
            total["work"] = work[phase]
        else:
            # Diagnostic partial endpoint only, never a completed owner total.
            partial = [item for item in valid if nonnegative_integer(item.get("work_cumulative"))]
            if partial:
                total["partial_work_endpoint"] = partial[-1]["work_cumulative"]
        phase_totals[phase] = total
    return {"records": records, "errors": errors, "phases": phase_totals,
            "work": work, "input": input_records[0] if len(input_records) == 1 else None,
            "complete": not errors}


def external_time(path):
    if not path.exists():
        return None
    for line in reversed(path.read_text(errors="replace").splitlines()):
        try:
            value = json.loads(line)
            if isinstance(value, dict) and "peak_rss_kib" in value:
                return value
        except json.JSONDecodeError:
            pass
    return None


def one_run(case, mode, repetition, warmup, output, options, base, required_phases):
    label = "warmup" if warmup else "measured"
    directory = output / case["id"] / f"{label}-{repetition:03d}-{mode}"
    directory.mkdir(parents=True, exist_ok=False)
    stdout, stderr, time_file = (directory / name for name in
                                ("stdout.log", "stderr.log", "time.json"))
    cwd = Path(case.get("cwd", base))
    if not cwd.is_absolute():
        cwd = base / cwd
    cwd = cwd.resolve()
    argv = [str(item) for item in case["argv"]]
    executable = shutil.which(argv[0]) if "/" not in argv[0] else str((cwd / argv[0]).resolve())
    executable = executable or str((cwd / argv[0]).resolve())
    if Path(executable).name.startswith(("cargo", "rustc", "rustup")):
        raise ValueError("runner accepts already-built executables, not compiler/build commands")
    argv[0] = str(Path(executable).resolve())
    executable_before = sha(executable) if Path(executable).is_file() else None
    immutable_paths = list(dict.fromkeys([*case.get("input_paths", []), *case.get("test_source_paths", [])]))
    before = snapshot(immutable_paths, base)
    environment = os.environ.copy()
    environment.update({str(key): str(value) for key, value in case.get("env", {}).items()})
    environment["ASH_CALIBRATION_OBSERVE"] = "1" if mode == "on" else "0"
    environment["ASH_CALIBRATION_LIMIT"] = str(options.limit)
    command = ["/usr/bin/time", "-f", TIME_FORMAT, "-o", str(time_file), "--", *argv]
    started, started_utc = time.monotonic(), utc_now()
    timed_out, spawn_error, exit_code = False, None, None
    with stdout.open("wb") as out, stderr.open("wb") as err:
        child_cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
        try:
            process = subprocess.Popen(command, cwd=cwd, env=environment,
                                       stdout=out, stderr=err, start_new_session=True)
            try:
                exit_code = process.wait(timeout=case.get("timeout", options.timeout))
            except subprocess.TimeoutExpired:
                timed_out = True
                try:
                    os.killpg(process.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    exit_code = process.wait(timeout=1)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    exit_code = process.wait()
        except OSError as error:
            spawn_error = str(error)
        child_cpu_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    child_cpu = {
        "source": "resource.getrusage(resource.RUSAGE_CHILDREN)",
        "units": "CPU seconds; native platform precision, stored without decimal rounding",
        "before": {"user_seconds": child_cpu_before.ru_utime, "system_seconds": child_cpu_before.ru_stime},
        "after": {"user_seconds": child_cpu_after.ru_utime, "system_seconds": child_cpu_after.ru_stime},
        "user_seconds": child_cpu_after.ru_utime - child_cpu_before.ru_utime,
        "system_seconds": child_cpu_after.ru_stime - child_cpu_before.ru_stime,
        "ownership": "GNU time wrapper and reaped target/descendant processes; excludes Python runner CPU",
    }
    child_cpu["total_seconds"] = child_cpu["user_seconds"] + child_cpu["system_seconds"]
    elapsed = time.monotonic() - started
    after = snapshot(immutable_paths, base)
    observation = records_from_logs(stdout, stderr, mode == "on", required_phases)
    timing = external_time(time_file)
    issues = list(observation["errors"])
    if "expected_stdout" in case and stdout.read_text(errors="replace").strip() != case["expected_stdout"].strip():
        issues.append("stdout does not match the manifest's expected program value")
    harness = None
    if "expected_test_count" in case:
        combined = stdout.read_text(errors="replace") + "\n" + stderr.read_text(errors="replace")
        matches = re.findall(r"test result: (ok|FAILED)\. (\d+) passed; (\d+) failed; (\d+) ignored;", combined)
        harness = [{"status": match[0], "passed": int(match[1]), "failed": int(match[2]),
                    "ignored": int(match[3])} for match in matches]
        expected = case["expected_test_count"]
        if len(harness) != 1 or harness[0] != {"status": "ok", "passed": expected, "failed": 0, "ignored": 0}:
            issues.append(f"native harness must report exactly {expected} passed, zero failed/ignored; found {harness}")
    if timed_out:
        issues.append("process group exceeded external timeout")
    if spawn_error:
        issues.append(f"process spawn failed: {spawn_error}")
    if exit_code != case.get("expected_exit", 0):
        issues.append(f"exit {exit_code}; expected {case.get('expected_exit', 0)}")
    if timing is None:
        issues.append("missing external GNU time record")
    elif any(not numeric(timing.get(key)) or timing[key] < 0 for key in
             ("wall_seconds", "user_seconds", "system_seconds", "peak_rss_kib")):
        issues.append("invalid external GNU time measurements")
    if before != after or any("error" in item for item in before):
        issues.append("declared immutable inputs missing or changed during run")
    actual_hashes = {item["path"]: item.get("sha256") for item in before}
    for field in ("input_sha256", "test_source_sha256"):
        for declared_path, expected_hash in case.get(field, {}).items():
            path = Path(declared_path)
            path = path if path.is_absolute() else base / path
            if actual_hashes.get(str(path.resolve())) != expected_hash:
                issues.append(f"{field}: pinned input hash mismatch: {path}")
    executable_after = sha(executable) if Path(executable).is_file() else None
    if executable_before is None or executable_before != executable_after:
        issues.append("executable missing or changed during run")
    record = {"case": case["id"], "family": case["family"], "parameters": case.get("parameters", {}),
              "features": case.get("features", {}), "held_out": case.get("held_out", False),
              "mode": mode, "repetition": repetition, "warmup": warmup,
              "started_utc": started_utc, "argv": argv, "cwd": str(cwd),
              "executable_sha256": executable_before, "executable_sha256_after": executable_after,
              "diagnostic_base_limit": options.limit,
              "expected_exit": case.get("expected_exit", 0), "exit_code": exit_code,
              "native_harness": harness,
              "timed_out": timed_out, "spawn_error": spawn_error,
              "runner_elapsed_seconds": elapsed, "external_time": timing,
              "wrapper_inclusive_child_cpu": child_cpu,
              "inputs_before": before, "inputs_after": after,
              "stdout": {"path": str(stdout), "sha256": sha(stdout)},
              "stderr": {"path": str(stderr), "sha256": sha(stderr)},
              "time_record": {"path": str(time_file), "sha256": sha(time_file) if time_file.exists() else None},
              "observation": observation, "issues": issues, "valid": not issues}
    dump(directory / "result.json", record)
    return record


def load_manifest(path):
    manifest = json.loads(path.read_text())
    if isinstance(manifest, list):
        manifest = {"cases": manifest}
    if not isinstance(manifest, dict) or not isinstance(manifest.get("cases"), list):
        raise ValueError("manifest must contain a cases array")
    names = manifest.get("model_features", MODEL_FEATURES)
    if not isinstance(names, (list, tuple)) or not names or any(not isinstance(name, str) for name in names) or len(set(names)) != len(names):
        raise ValueError("model_features must be distinct nonempty feature names")
    ids = set()
    for case in manifest["cases"]:
        if not isinstance(case, dict) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", case.get("id", "")):
            raise ValueError("case id must be a safe nonempty filename")
        if case["id"] in ids:
            raise ValueError(f"duplicate case id: {case['id']}")
        ids.add(case["id"])
        if not isinstance(case.get("family"), str) or not case["family"]:
            raise ValueError(f"{case['id']}: missing family")
        if not isinstance(case.get("argv"), list) or not case["argv"] or any(not isinstance(arg, str) for arg in case["argv"]):
            raise ValueError(f"{case['id']}: missing argv")
        if not isinstance(case.get("expected_exit", 0), int):
            raise ValueError(f"{case['id']}: expected_exit must be an integer")
        if "expected_test_count" in case and (not nonnegative_integer(case["expected_test_count"]) or case["expected_test_count"] < 1):
            raise ValueError(f"{case['id']}: expected_test_count must be a positive integer")
        if "expected_stdout" in case and not isinstance(case["expected_stdout"], str):
            raise ValueError(f"{case['id']}: expected_stdout must be a string")
        if "timeout" in case and (not numeric(case["timeout"]) or case["timeout"] <= 0):
            raise ValueError(f"{case['id']}: timeout must be finite and positive")
        for key in ("parameters", "features", "env"):
            if not isinstance(case.get(key, {}), dict):
                raise ValueError(f"{case['id']}: {key} must be an object")
        for key in ("input_sha256", "test_source_sha256"):
            if not isinstance(case.get(key, {}), dict):
                raise ValueError(f"{case['id']}: {key} must be a path/hash object")
        if not isinstance(case.get("held_out", False), bool):
            raise ValueError(f"{case['id']}: held_out must be boolean")
        if any(phase not in PHASES + OPTIONAL_PHASES for phase in case.get("required_phases", manifest.get("required_phases", PHASES))):
            raise ValueError(f"{case['id']}: unknown required phase")
    return manifest


def feature_vector(record):
    result = dict(record.get("features", {}))
    measured = record["observation"].get("input")
    if measured:
        result.update(measured.get("features", {}))
    result = {key: value for key, value in result.items() if numeric(value) and value >= 0}
    for output, left, right in [("type_depth_product", "type_nodes", "type_depth"),
                                ("import_depth_product", "imports", "module_depth"),
                                ("resource_size_product", "resource_sites", "nodes")]:
        if left in result and right in result:
            result[output] = result[left] * result[right]
    return result


def fit_model(rows, names, cap):
    """Scaled least squares with rank detection; never borrow held-out rows."""
    usable = [row for row in rows if all(name in row["features"] for name in names)]
    train = [row for row in usable if not row["held_out"]]
    held = [row for row in usable if row["held_out"]]
    width = len(names) + 1
    model = {"features": ["intercept", *names], "training_cases": len(train),
             "held_out_cases": len(held), "missing_feature_cases": len(rows) - len(usable),
             "headroom": 2, "finite_cap": cap, "status": "insufficient-data"}
    if not train:
        return model
    scales = [max(1.0, max(abs(row["features"][name]) for row in train)) for name in names]
    design = [[1.0, *(row["features"][name] / scale for name, scale in zip(names, scales))]
              for row in train]
    # Pivoted modified Gram-Schmidt avoids squaring the condition number.
    columns = [[row[index] for row in design] for index in range(width)]
    permutation = list(range(width))
    q_vectors, triangular = [], [[0.0] * width for _ in range(width)]
    initial_norm = max(math.sqrt(sum(x * x for x in column)) for column in columns)
    for index in range(width):
        pivot = max(range(index, width), key=lambda j: sum(x * x for x in columns[j]))
        columns[index], columns[pivot] = columns[pivot], columns[index]
        permutation[index], permutation[pivot] = permutation[pivot], permutation[index]
        for previous in range(index):
            triangular[previous][index], triangular[previous][pivot] = triangular[previous][pivot], triangular[previous][index]
        norm = math.sqrt(sum(x * x for x in columns[index]))
        if norm <= max(1e-12, initial_norm * 1e-10):
            break
        triangular[index][index] = norm
        q = [x / norm for x in columns[index]]
        q_vectors.append(q)
        for next_index in range(index + 1, width):
            coefficient = sum(a * b for a, b in zip(q, columns[next_index]))
            triangular[index][next_index] = coefficient
            columns[next_index] = [b - coefficient * a for a, b in zip(q, columns[next_index])]
    rank = len(q_vectors)
    model.update({"rank": rank, "parameters": width, "training_families": sorted({row["family"] for row in train})})
    if rank != width:
        model["status"] = "rank-insufficient"
        return model
    if len(train) < max(8, 2 * width) or len(model["training_families"]) < 2:
        model["status"] = "sample-insufficient"
        return model
    target = [row["value"] for row in train]
    projected = [sum(a * b for a, b in zip(q, target)) for q in q_vectors]
    coefficients = [0.0] * width
    for index in reversed(range(width)):
        coefficients[index] = (projected[index] - sum(triangular[index][j] * coefficients[j]
                              for j in range(index + 1, width))) / triangular[index][index]
    reordered = [0.0] * width
    for index, original in enumerate(permutation):
        reordered[original] = coefficients[index]
    # A larger immutable feature must not reduce a proposed allowance.
    # Coordinate descent solves the small nonnegative least-squares problem.
    scaled_coefficients = [max(0.0, value) for value in reordered]
    for iteration in range(20000):
        largest_change = 0.0
        for column in range(width):
            denominator = sum(row[column] ** 2 for row in design)
            numerator = sum(row[column] * (value - sum(row[j] * scaled_coefficients[j]
                            for j in range(width) if j != column))
                            for row, value in zip(design, target))
            updated = max(0.0, numerator / denominator) if denominator else 0.0
            largest_change = max(largest_change, abs(updated - scaled_coefficients[column]))
            scaled_coefficients[column] = updated
        if largest_change < 1e-10 * max(1.0, max(scaled_coefficients)):
            break
    model["nonnegative_fit_iterations"] = iteration + 1
    model["nonnegative_fit_converged"] = iteration < 19999
    coefficients = [scaled_coefficients[0], *(value / scale for value, scale in zip(scaled_coefficients[1:], scales))]

    def predict(row):
        return coefficients[0] + sum(coefficients[i + 1] * row["features"][name]
                                     for i, name in enumerate(names))

    cushion = max(0.0, max(row["value"] - predict(row) for row in train))
    estimates = []
    for row in usable:
        raw = predict(row)
        uncapped = 2 * max(1.0, raw + cushion)
        envelope = min(cap, math.ceil(uncapped))
        estimates.append({"case": row["case"], "held_out": row["held_out"],
                          "observed": row["value"], "predicted": raw,
                          "residual": row["value"] - raw, "envelope": envelope,
                          "uncapped_envelope": uncapped, "cap_binding": uncapped > cap,
                          "covered": row["value"] <= envelope})
    model.update({"status": "provisional", "coefficients": dict(zip(["intercept", *names], coefficients)),
                  "training_positive_residual_cushion": cushion, "cases": estimates,
                  "training_rmse": math.sqrt(sum((row["value"] - predict(row)) ** 2 for row in train) / len(train)),
                  "held_out_rmse": math.sqrt(sum((row["value"] - predict(row)) ** 2 for row in held) / len(held)) if held else None,
                  "training_coverage": sum(item["covered"] for item in estimates if not item["held_out"]) / len(train),
                  "held_out_coverage": sum(item["covered"] for item in estimates if item["held_out"]) / len(held) if held else None,
                  "limitations": ["Empirical sampled-domain envelope, not a universal bound or production policy.",
                                  "Nonnegative coefficients preserve predictor monotonicity, not universal cost coverage.",
                                  "Twofold headroom follows a training-only positive residual cushion; finite cap may prevent coverage."]})
    return model


def growth_evidence(case_summaries, phase):
    groups = {}
    for case in case_summaries:
        value = case.get("work", {}).get(phase)
        if not value:
            continue
        parameters = case["parameters"]
        for varied, x in parameters.items():
            if not numeric(x) or x <= 0:
                continue
            fixed = tuple(sorted((key, json.dumps(item, sort_keys=True)) for key, item in parameters.items() if key != varied))
            groups.setdefault((case["family"], varied, fixed), []).append((x, value["median"], case["id"]))
    result = []
    for (family, parameter, fixed), points in sorted(groups.items()):
        points.sort()
        edges = []
        for (x1, y1, id1), (x2, y2, id2) in zip(points, points[1:]):
            if x2 <= x1 or y1 <= 0 or y2 <= 0:
                continue
            exponent = math.log(y2 / y1) / math.log(x2 / x1)
            edges.append({"from": id1, "to": id2, "parameter_ratio": x2 / x1,
                          "work_ratio": y2 / y1, "empirical_power": exponent})
        if edges:
            result.append({"family": family, "parameter": parameter, "fixed_parameters": dict(fixed),
                           "edges": edges, "faster_than_quadratic_observed": any(edge["empirical_power"] > 2.5 for edge in edges),
                           "note": "Pairwise finite-range growth; no asymptotic or exponential conclusion from these points."})
    return result


def make_report(output):
    run_manifest = json.loads((output / "run-manifest.json").read_text())
    records = [json.loads(line) for line in (output / "runs.jsonl").read_text().splitlines() if line]
    measured = [record for record in records if not record["warmup"]]
    cases, failures = [], []
    for case in run_manifest["manifest"]["cases"]:
        own = [record for record in measured if record["case"] == case["id"]]
        if not own:
            continue
        on = [record for record in own if record["mode"] == "on"]
        off = [record for record in own if record["mode"] == "off"]
        issues = [f"{record['mode']} repetition {record['repetition']}: {issue}"
                  for record in own for issue in record["issues"]]
        vectors = [feature_vector(record) for record in on if record["valid"]]
        if vectors and any(vector != vectors[0] for vector in vectors[1:]):
            issues.append("immutable feature vector varies between repeated processes")
        identities = [(record["executable_sha256"], record["inputs_before"]) for record in own]
        if identities and any(item != identities[0] for item in identities[1:]):
            issues.append("executable/input hashes vary between controls and observations")
        if not on or not off:
            issues.append("both observation-on and observation-off controls are required for acceptance")
        repetitions = run_manifest["options"]["repetitions"]
        if len(on) != repetitions or len(off) != repetitions:
            issues.append("incomplete requested observation/control repetition set")
        if any(not record["valid"] for record in own):
            issues.append("not all measured processes produced controlled valid records")
        if case.get("expected_exit", 0) != 0:
            issues.append("expected rejection is preserved but is not a successful scaling observation")
        accepted = not issues
        item = {"id": case["id"], "family": case["family"], "parameters": case.get("parameters", {}),
                "held_out": case.get("held_out", False), "accepted_for_models": accepted,
                "issues": issues, "features": vectors[0] if vectors else {}, "process": {},
                "phase_wall_ns": {}, "work": {}, "phase_rss_boundaries": {}}
        for mode, subset in (("on", on), ("off", off)):
            valid = [record for record in subset if record["valid"]]
            item["process"][mode] = {key: summarize(record["external_time"].get(key) for record in valid)
                                     for key in ("wall_seconds", "user_seconds", "system_seconds", "peak_rss_kib")}
            for key in ("user_seconds", "system_seconds", "total_seconds"):
                item["process"][mode]["wrapper_inclusive_child_" + key] = summarize(
                    record.get("wrapper_inclusive_child_cpu", {}).get(key) for record in valid)
        overhead = {}
        for key in ("wall_seconds", "user_seconds", "system_seconds", "peak_rss_kib",
                    "wrapper_inclusive_child_user_seconds", "wrapper_inclusive_child_system_seconds",
                    "wrapper_inclusive_child_total_seconds"):
            a, b = item["process"]["on"][key], item["process"]["off"][key]
            overhead[key] = {"median_difference": a["median"] - b["median"],
                             "median_ratio": a["median"] / b["median"] if b["median"] else None} if a and b else None
        item["observer_overhead"] = overhead
        for phase in PHASES + OPTIONAL_PHASES:
            endpoints = [record["observation"]["phases"][phase] for record in on
                         if record["valid"] and phase in record["observation"]["phases"]]
            item["phase_wall_ns"][phase] = summarize(endpoint["wall_ns"] for endpoint in endpoints)
            item["phase_rss_boundaries"][phase] = [endpoint["rss_boundaries"] for endpoint in endpoints]
            owner = [record["observation"]["work"][phase] for record in on
                     if record["valid"] and phase in record["observation"]["work"]]
            if owner:
                values = [record["work_cumulative"] for record in owner]
                item["work"][phase] = summarize(values)
                item.setdefault("limits", {})[phase] = [{key: record[key] for key in
                                                         ("normal_limit", "diagnostic_limit")} for record in owner]
                if len(set(values)) != 1:
                    item.setdefault("work_variation", {})[phase] = {"min": min(values), "max": max(values), "note": "Raw charged work varies across fresh processes; no normalization applied."}
        if item["issues"]:
            failures.append({"case": case["id"], "issues": item["issues"]})
        cases.append(item)
    models = {}
    names = run_manifest["manifest"].get("model_features", list(MODEL_FEATURES))
    cap = run_manifest["options"]["model_cap"]
    for phase in LEDGERS:
        rows = [{"case": case["id"], "family": case["family"], "features": case["features"],
                 "held_out": case["held_out"], "value": case["work"][phase]["median"]}
                for case in cases if case["accepted_for_models"] and phase in case["work"]]
        models[phase] = {"simple_size": fit_model(rows, ["nodes"], cap),
                         "measured_complexity": fit_model(rows, names, cap),
                         "size_type_depth": fit_model(rows, ["nodes", "type_depth_product"], cap),
                         "source_interactions": fit_model(rows, ["nodes", "type_depth_product", "import_depth_product", "resource_size_product"], cap),
                         "family_growth": growth_evidence([case for case in cases if case["accepted_for_models"]], phase)}
    report = {"created_utc": utc_now(), "provenance": run_manifest,
              "cases": cases, "models": models, "failures": failures,
              "raw_run_count": len(records), "measured_run_count": len(measured),
              "warmup_run_count": len(records) - len(measured),
              "interpretation": ["External time excludes builds; each observation has a fresh process.",
                                 "GNU time target user/system CPU seconds and process peak RSS remain separate measurements; printed CPU precision may round short runs to zero.",
                                 "Wrapper-inclusive child CPU uses serial RUSAGE_CHILDREN before/after deltas in seconds, retaining native platform precision without decimal rounding.",
                                 "These child CPU deltas include GNU time and reaped target descendants, exclude Python runner CPU, and do not isolate individual compiler phases.",
                                 "Child accounting requires descendants to be waited for; a killed wrapper can omit orphaned descendants after timeout. Failed runs remain evidence, not model inputs.",
                                 "CPU is scheduled processor time, separate from wall duration, structural work units and allocation counts; threaded child CPU can exceed wall duration.",
                                 "Boundary RSS is not a phase peak; process peak RSS is cumulative.",
                                 "Phase wall sums can overlap with containing phases; do not sum them into pipeline time.",
                                 "Missing or aborted work endpoints are absent, never zero.",
                                 "Envelopes use each case maximum raw work, preserving fresh-process capacity variation.",
                                 "GNU time wall and CPU values have centisecond resolution; phase timers have finer resolution.",
                                 "Both observer modes retain feature-enabled budget override machinery.",
                                 "Controls use the same executable and finite diagnostic allowance as observation-on.",
                                 "Models exclude failed, uncontrolled and held-out cases from fitting.",
                                 "Family growth must be reviewed before adopting any empirical envelope."]}
    dump(output / "summary.json", report)
    lines = ["# Resource calibration measurements", "", "Experimental measurements; no production policy change.", "",
             "| Case | Eligible for fitting | Charged Source | Charged Core | Wall on/off median seconds | Peak RSS on/off KiB |",
             "| --- | --- | ---: | ---: | --- | --- |"]

    def median(value):
        return str(value["median"]) if value else "missing"

    for case in cases:
        process = case["process"]
        lines.append(f"| {case['id']} | {case['accepted_for_models']} | {median(case['work'].get('source-checking'))} | "
                     f"{median(case['work'].get('independent-effect-core'))} | "
                     f"{median(process['on']['wall_seconds'])} / {median(process['off']['wall_seconds'])} | "
                     f"{median(process['on']['peak_rss_kib'])} / {median(process['off']['peak_rss_kib'])} |")
    lines.extend(["", "Each six-owner work vector, phase boundary RSS, median/min/max, observer overhead, failures, models, residuals and held-out coverage is in `summary.json`.", "",
                  "CPU summaries preserve GNU time's target measurements and separately report wrapper-inclusive child user/system/total CPU seconds from native-precision `RUSAGE_CHILDREN` deltas. The latter include GNU time and reaped descendants, exclude Python runner CPU, and measure no individual compiler phase. Raw cumulative before/after CPU readings and deltas are retained in each run. Older evidence without these fields stays missing.", "",
                  "Models use each case's maximum observed admission charge. Held-out cases remain excluded from fitting even when eligible. Charges include precharged capacity and are not machine instruction counts. The simple model uses source nodes; the enriched model uses named immutable graph features. A fitted model is provisional: its envelope is twice the sum of its fitted value and training-only positive residual cushion, with a finite cap. Rank or sample insufficiency prevents an allowance estimate.", ""])
    for phase, model in models.items():
        lines.append(f"- {phase}: size {model['simple_size']['status']}; complexity {model['measured_complexity']['status']}.")
    if failures:
        lines.extend(["", "## Incomplete or uncontrolled cases", ""])
        for failure in failures:
            lines.append(f"- {failure['case']}: {'; '.join(failure['issues'])}")
    lines.extend(["", *report["interpretation"], ""])
    (output / "report.md").write_text("\n".join(lines))
    return report


def run(options):
    path, output = options.manifest.resolve(), options.output.resolve()
    manifest = load_manifest(path)
    if options.case:
        pattern = re.compile(options.case)
        manifest["cases"] = [case for case in manifest["cases"] if pattern.search(case["id"])]
    if not manifest["cases"]:
        raise ValueError("no cases selected")
    output.mkdir(parents=True, exist_ok=False)
    dump(output / "run-manifest.json", {"created_utc": utc_now(), "manifest_path": str(path),
                                       "manifest_sha256": sha(path), "manifest": manifest,
                                       "runner_sha256": sha(__file__), "python": sys.version,
                                       "options": {key: value for key, value in vars(options).items()
                                                   if key not in ("func", "manifest", "output")}})
    records_path = output / "runs.jsonl"
    frozen = False
    with records_path.open("a") as stream:
        for case in sorted(manifest["cases"], key=lambda item: item.get("held_out", False)):
            if case.get("held_out", False) and not frozen:
                training_report = make_report(output)
                dump(output / "frozen-training-models.json", {
                    "created_utc": utc_now(), "models": training_report["models"],
                    "note": "Frozen before executing any held-out case; coefficients use only completed training observations.",
                })
                frozen = True
            phases = case.get("required_phases", manifest.get("required_phases", PHASES))
            for warmup, count in ((True, options.warmups), (False, options.repetitions)):
                for repetition in range(count):
                    # Alternate ordering to reduce a systematic observation-on temperature bias.
                    modes = options.modes if repetition % 2 == 0 else list(reversed(options.modes))
                    for mode in modes:
                        record = one_run(case, mode, repetition, warmup, output, options, path.parent, phases)
                        stream.write(json.dumps(record, sort_keys=True) + "\n")
                        stream.flush()
                        print(f"{case['id']} {'warmup' if warmup else 'measured'} {repetition} {mode}: "
                              f"{'valid' if record['valid'] else '; '.join(record['issues'])}", flush=True)
    report = make_report(output)
    return 1 if report["failures"] or any(not json.loads(line)["valid"] for line in records_path.read_text().splitlines()) else 0


def self_check(_options):
    """One connected fake executable exercises collection, refusal and controls."""
    child = r'''import json,os,sys,time
if sys.argv[1] == "timeout": time.sleep(10)
if os.environ.get("ASH_CALIBRATION_OBSERVE") == "1":
 def emit(x): print("ASH_CALIBRATION "+json.dumps(x),file=sys.stderr)
 width=int(sys.argv[2])
 emit({"event":"input","features":{"nodes":width,"bytes":4*width}})
 phases="loading resolution source-checking module-linking linked-interface final-elaboration independent-effect-core evaluation pipeline".split()
 for p in phases:
  emit({"event":"phase","phase":p,"wall_ns":1000,"rss_start_kib":100,"rss_end_kib":110,"process_peak_rss_kib":120,"completed":True})
  if p not in ["loading","evaluation","pipeline"]:
   emit({"event":"work","phase":p,"work_cumulative":12*width,"normal_limit":327680,"diagnostic_limit":int(os.environ["ASH_CALIBRATION_LIMIT"])})
 if sys.argv[1] == "malformed": print("ASH_CALIBRATION {",file=sys.stderr)
print("test result: ok. "+("0" if sys.argv[1]=="zero-tests" else "1")+" passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;")
'''
    with tempfile.TemporaryDirectory(prefix="ash-calibration-self-check-") as temporary:
        base = Path(temporary)
        executable = base / "child.py"
        executable.write_text(child)
        manifest = base / "manifest.json"
        samples = [{"id": f"{family}-{width}", "family": family,
                    "parameters": {"width": width}, "held_out": width == 6,
                    "argv": [sys.executable, str(executable), "valid", str(width)],
                    "input_paths": [str(executable)], "expected_test_count": 1}
                   for family in ("flat", "depth") for width in (1, 2, 3, 4, 6)]
        samples.extend({"id": kind, "family": "connected-self-check", "parameters": {},
                        "argv": [sys.executable, str(executable), kind, "1"],
                        "input_paths": [str(executable)], "expected_test_count": 1,
                        **({"timeout": 0.05} if kind == "timeout" else {})}
                       for kind in ("malformed", "timeout", "zero-tests"))
        dump(manifest, {"cases": samples, "model_features": ["nodes", "bytes"]})
        options = argparse.Namespace(manifest=manifest, output=base / "result", case=None,
                                     warmups=0, repetitions=1, timeout=2, limit=1024,
                                     modes=["on", "off"], model_cap=4096)
        assert run(options) == 1
        report = json.loads((options.output / "summary.json").read_text())
        raw = [json.loads(line) for line in (options.output / "runs.jsonl").read_text().splitlines()]
        for record in raw:
            cpu = record["wrapper_inclusive_child_cpu"]
            assert all(numeric(cpu[key]) and cpu[key] >= 0 for key in ("user_seconds", "system_seconds", "total_seconds"))
            assert cpu["user_seconds"] == cpu["after"]["user_seconds"] - cpu["before"]["user_seconds"]
            assert cpu["system_seconds"] == cpu["after"]["system_seconds"] - cpu["before"]["system_seconds"]
        assert any(record["wrapper_inclusive_child_cpu"]["total_seconds"] > 0 for record in raw)
        cases = {case["id"]: case for case in report["cases"]}
        assert cases["flat-1"]["accepted_for_models"]
        for mode in ("on", "off"):
            stats = cases["flat-1"]["process"][mode]["wrapper_inclusive_child_total_seconds"]
            assert stats["n"] == 1 and stats["min"] == stats["median"] == stats["max"]
        assert not cases["malformed"]["accepted_for_models"]
        assert not cases["timeout"]["accepted_for_models"]
        assert not cases["zero-tests"]["accepted_for_models"]
        assert not cases["timeout"]["work"]
        assert any("invalid observer JSON" in issue for issue in cases["malformed"]["issues"])
        assert any("timeout" in issue for issue in cases["timeout"]["issues"])
        size = report["models"]["source-checking"]["simple_size"]
        assert size["status"] == "provisional" and size["training_cases"] == 8
        assert size["held_out_cases"] == 2 and size["held_out_coverage"] == 1
        assert abs(size["coefficients"]["nodes"] - 12) < 1e-6
        assert report["models"]["source-checking"]["measured_complexity"]["status"] == "rank-insufficient"
    print("Connected runner self-check passed; no Ash compiler/build invoked.")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    command = commands.add_parser("run", help="run a manifest against already-built executables")
    command.add_argument("manifest", type=Path)
    command.add_argument("--output", type=Path, required=True)
    command.add_argument("--warmups", type=int, default=1)
    command.add_argument("--repetitions", type=int, default=3)
    command.add_argument("--timeout", type=float, default=30)
    command.add_argument("--limit", type=int, default=16_777_216)
    command.add_argument("--model-cap", type=int, default=16_777_216)
    command.add_argument("--case", help="regular expression matching case ids")
    command.add_argument("--modes", type=lambda value: value.split(","), default=["on", "off"])
    command.set_defaults(func=run)
    command = commands.add_parser("report", help="recompute summary from preserved raw runs")
    command.add_argument("output", type=Path)
    command.set_defaults(func=lambda options: (make_report(options.output.resolve()), 0)[1])
    command = commands.add_parser("self-check", help="connected Python-only runner regression check")
    command.set_defaults(func=self_check)
    options = parser.parse_args()
    if options.command == "run":
        if options.warmups < 0 or options.repetitions < 1 or not numeric(options.timeout) or options.timeout <= 0:
            parser.error("warmups >= 0, repetitions >= 1 and finite positive timeout required")
        if not 0 < options.limit <= sys.maxsize or not 0 < options.model_cap <= sys.maxsize:
            parser.error("diagnostic limit and model cap must be finite positive host-size integers")
        if not options.modes or len(set(options.modes)) != len(options.modes) or set(options.modes) - {"on", "off"}:
            parser.error("modes must be on,off or one selected control mode")
    try:
        return options.func(options)
    except (ValueError, OSError, KeyError) as error:
        print(f"resource calibration: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
