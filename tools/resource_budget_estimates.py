#!/usr/bin/env python3
"""Offline rough cost budgets: fixed + b*nodes + c*type_nodes*type_depth
+ d*resource_sites*nodes. Budgets predict typical cost; refusal limits are separate.
"""
import argparse
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import resource_calibration as collector

RAW = ("nodes", "type_nodes", "type_depth", "resource_sites")
TERMS = ("nodes", "type_depth_product", "resource_size_product")
RESPONSES = {**{phase: "charged units, including reservations" for phase in collector.LEDGERS},
             "cpu_seconds": "observation-off wrapper-inclusive child CPU seconds",
             "peak_rss_kib": "observation-off GNU time process peak RSS KiB"}


def features(value):
    raw = value.get("features", value)
    if any(not collector.numeric(raw.get(key)) or raw[key] < 0 for key in RAW):
        raise ValueError("features require finite nonnegative nodes, type_nodes, type_depth, resource_sites")
    result = {**{key: raw[key] for key in RAW},
              "type_depth_product": raw["type_nodes"] * raw["type_depth"],
              "resource_size_product": raw["resource_sites"] * raw["nodes"]}
    if any(not collector.numeric(value) for value in result.values()):
        raise ValueError("feature products must remain finite")
    return result


def actual(case, response):
    if response in collector.LEDGERS:
        value = case.get("work", {}).get(response)
    else:
        key = "wrapper_inclusive_child_total_seconds" if response == "cpu_seconds" else "peak_rss_kib"
        value = case.get("process", {}).get("off", {}).get(key)
    return value.get("median") if isinstance(value, dict) else None


def errors(rows):
    residuals = [row["actual"] - row["predicted"] for row in rows]
    ratios = [row["actual"] / row["predicted"] for row in rows if row["predicted"] > 0]
    return {"rmse": math.sqrt(sum(value * value for value in residuals) / len(rows)) if rows else None,
            "residuals": collector.summarize(residuals), "actual_to_predicted_ratios": collector.summarize(ratios),
            "zero_prediction_cases": [row["case"] for row in rows if row["predicted"] == 0], "cases": rows}


def point(coefficients, vector):
    return coefficients["intercept"] + sum(coefficients[key] * vector[key] for key in TERMS)


def fit_summary(summary):
    cases = [case for case in summary["cases"] if case.get("accepted_for_models")]
    vectors = {case["id"]: features(case) for case in cases}
    model = {"formula": "fixed_cost + b*nodes + c*(type_nodes*type_depth) + d*(resource_sites*nodes)",
             "training_case_count": len(cases), "training_case_ids": [case["id"] for case in cases],
             "excluded_case_ids": [case["id"] for case in summary["cases"] if not case.get("accepted_for_models")],
             "feature_ranges": {key: {"min": min(v[key] for v in vectors.values()),
                                      "max": max(v[key] for v in vectors.values())} for key in (*RAW, *TERMS[1:])} if cases else {},
             "responses": {}, "interpretation": [
                 "Explicit recalibration: all completed cases are training data; earlier held-out results have been examined.",
                 "One case median per response; repetitions are not independent training cases.",
                 "Coefficients are nonnegative; the four-term form is fixed, with no feature selection or rescue fit.",
                 "Charged work includes reservations and remains a proxy; CPU and RSS retain separate physical units.",
                 "Point predictions only: no headroom, envelope, cap, stopping policy or automatic limit adjustment.",
                 "Observed ranges are axis-aligned checks, not proof that new combinations interpolate safely."]}
    for response, units in RESPONSES.items():
        rows = [{"case": case["id"], "family": case["family"], "features": vectors[case["id"]],
                 "held_out": False, "value": actual(case, response)} for case in cases]
        missing = [row["case"] for row in rows if not collector.numeric(row["value"]) or row["value"] < 0]
        if missing:
            model["responses"][response] = {"status": "missing-response", "cases": missing, "units": units}
            continue
        # The existing helper computes envelopes too; none enter this artifact or prediction.
        fitted = collector.fit_model(rows, list(TERMS), sys.maxsize)
        result = {"units": units, "status": fitted["status"],
                  **{key: fitted[key] for key in ("rank", "parameters", "nonnegative_fit_iterations", "nonnegative_fit_converged") if key in fitted}}
        if "coefficients" in fitted:
            coefficients = fitted["coefficients"]
            assert all(value >= 0 for value in coefficients.values())
            result["coefficients"] = coefficients
            result["observed_range"] = collector.summarize(row["value"] for row in rows)
            result["fit_errors"] = errors([{"case": row["case"], "actual": row["value"],
                                            "predicted": point(coefficients, row["features"])} for row in rows])
            if not fitted.get("nonnegative_fit_converged", False):
                result["status"] = "not-converged"
        model["responses"][response] = result
    return model


def prediction(model, value):
    vector = features(value)
    outside = {key: {"value": vector[key], "observed": bounds} for key, bounds in model["feature_ranges"].items()
               if vector[key] < bounds["min"] or vector[key] > bounds["max"]}
    responses = {}
    for name, result in model["responses"].items():
        ready = "coefficients" in result and result["status"] != "not-converged"
        responses[name] = {"units": result["units"], "status": "point-estimate" if ready else result["status"],
                           "predicted": point(result["coefficients"], vector) if ready else None}
    return {"features": vector, "outside_observed_ranges": outside, "responses": responses,
            "interpretation": "Rough typical-cost prediction, not an admission allowance or limit adjustment."}


def evaluate(model, summary):
    rows = {name: [] for name in RESPONSES}
    excluded = []
    for case in summary["cases"]:
        if not case.get("accepted_for_models"):
            excluded.append(case["id"])
            continue
        estimated = prediction(model, case)
        for name, result in estimated["responses"].items():
            observed = actual(case, name)
            if result["predicted"] is not None and collector.numeric(observed):
                rows[name].append({"case": case["id"], "actual": observed, "predicted": result["predicted"],
                                   "outside_observed_ranges": estimated["outside_observed_ranges"]})
    return {"interpretation": "Descriptive comparison with existing examined evidence; no refitting and no claim of blind validation.",
            "excluded_case_ids": excluded, "responses": {name: errors(values) for name, values in rows.items()}}


def self_check():
    cases = []
    for index in range(12):
        raw = {"nodes": index + 1, "type_nodes": index % 3 + 1,
               "type_depth": index % 4 + 1, "resource_sites": index % 2}
        value = point({"intercept": 7, "nodes": 2, "type_depth_product": 3, "resource_size_product": 5}, features(raw))
        cases.append({"id": str(index), "family": str(index % 2), "accepted_for_models": True, "held_out": True,
                      "features": raw, "work": {phase: {"median": value} for phase in collector.LEDGERS},
                      "process": {"off": {"wrapper_inclusive_child_total_seconds": {"median": value}, "peak_rss_kib": {"median": value}}}})
    model = fit_summary({"cases": cases})
    predicted = prediction(model, {"nodes": 15, "type_nodes": 2, "type_depth": 3, "resource_sites": 1})
    assert predicted["outside_observed_ranges"]
    assert abs(predicted["responses"]["cpu_seconds"]["predicted"] - 130) < 1e-5
    assert model["responses"]["source-checking"]["fit_errors"]["rmse"] < 1e-5
    for case in cases:
        case["features"] = {"nodes": 1, "type_nodes": 1, "type_depth": 1, "resource_sites": 0}
    failed = fit_summary({"cases": cases})
    assert failed["responses"]["cpu_seconds"]["status"] == "rank-insufficient"
    assert prediction(failed, cases[0])["responses"]["cpu_seconds"]["predicted"] is None
    print("Connected offline additive-fit, prediction and rank-failure self-check passed.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    command = commands.add_parser("fit"); command.add_argument("summary", type=Path); command.add_argument("--output", type=Path, required=True)
    command = commands.add_parser("predict"); command.add_argument("model", type=Path); command.add_argument("features", type=Path)
    command = commands.add_parser("evaluate"); command.add_argument("model", type=Path); command.add_argument("summary", type=Path)
    commands.add_parser("self-check")
    args = parser.parse_args()
    if args.command == "self-check":
        self_check(); return
    if args.command == "fit":
        model = fit_summary(json.loads(args.summary.read_text()))
        model["provenance"] = {"summary_path": str(args.summary.resolve()), "summary_sha256": collector.sha(args.summary),
                               "estimator_sha256": collector.sha(__file__), "fitter_sha256": collector.sha(collector.__file__)}
        collector.dump(args.output, model)
        print(json.dumps({"output": str(args.output), "training_cases": model["training_case_count"],
                          "responses": {name: result["status"] for name, result in model["responses"].items()}}, indent=2))
    else:
        model = json.loads(args.model.read_text())
        result = prediction(model, json.loads(args.features.read_text())) if args.command == "predict" else evaluate(model, json.loads(args.summary.read_text()))
        result["model_sha256"] = collector.sha(args.model)
        result["input_sha256"] = collector.sha(args.features if args.command == "predict" else args.summary)
        print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError) as error:
        print(f"resource budgets: {error}", file=sys.stderr)
        raise SystemExit(2)
