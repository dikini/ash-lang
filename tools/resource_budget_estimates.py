#!/usr/bin/env python3
"""Offline rough cost budgets: fixed + b*nodes + c*type_nodes*type_depth
+ d*resource_sites*nodes. Physical review allowances and refusal limits are separate.
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
PHYSICAL = ("cpu_seconds", "peak_rss_kib")


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


def observation(case, response):
    if response in collector.LEDGERS:
        return case.get("work", {}).get(response)
    key = "wrapper_inclusive_child_total_seconds" if response == "cpu_seconds" else "peak_rss_kib"
    return case.get("process", {}).get("off", {}).get(key)


def actual(case, response):
    value = observation(case, response)
    return value.get("median") if isinstance(value, dict) else None


def errors(rows):
    residuals = [row["actual"] - row["predicted"] for row in rows]
    ratios = [row["actual"] / row["predicted"] for row in rows if row["predicted"] > 0]
    return {"rmse": math.sqrt(sum(value * value for value in residuals) / len(rows)) if rows else None,
            "residuals": collector.summarize(residuals), "actual_to_predicted_ratios": collector.summarize(ratios),
            "zero_prediction_cases": [row["case"] for row in rows if row["predicted"] == 0], "cases": rows}


def point(coefficients, vector):
    return coefficients["intercept"] + sum(coefficients[key] * vector[key] for key in TERMS)


def round_up(value, quantum):
    return math.ceil(value / quantum) * quantum


def calibrate(model, startup_summary, base_sha256, startup_sha256):
    """Retain the fitted model; attach an explicit, empirical decision policy."""
    controls = [case for case in startup_summary.get("cases", []) if case.get("id") == "flat-width0"]
    if (not startup_summary.get("complete") or startup_summary.get("interrupted") or len(controls) != 1
            or not controls[0].get("controlled_complete") or controls[0].get("issues")):
        raise ValueError("calibration requires one complete, valid flat-width0 startup control")
    measured = controls[0].get("language_metrics", {}).get("ash", {}).get("wrapper_child_total_seconds", {})
    median = measured.get("median")
    if not collector.numeric(median) or median <= 0 or not collector.numeric(measured.get("n")) or measured["n"] < 3:
        raise ValueError("startup control requires a positive CPU median from at least three measurements")
    if any("coefficients" not in model.get("responses", {}).get(name, {})
           or model["responses"][name].get("status") == "not-converged" for name in PHYSICAL):
        raise ValueError("calibration requires ready CPU and RSS point models")
    result = json.loads(json.dumps(model))
    result["interpretation"] = ["The following fit statements describe the unchanged raw base model; "
                                "decision_support_calibration adds separate physical floors and review allowances.",
                                *result.get("interpretation", [])]
    result["decision_support_calibration"] = {
        "schema": "physical-decision-support-v1",
        "provenance": {"base_model_sha256": base_sha256, "startup_summary_sha256": startup_sha256,
                       "estimator_sha256": collector.sha(__file__)},
        "startup_control": {"case": "flat-width0", "observed_cpu_seconds_median": median,
                            "measurement_count": measured["n"], "round_up_quantum_seconds": 0.005},
        "cpu_point_floor_seconds": round_up(median, 0.005),
        "review_thresholds": {
            "cpu_seconds": {"multiplier": 2.0, "offset": 0.01, "round_up_quantum": 0.01},
            "peak_rss_kib": {"multiplier": 1.5, "offset": 0.0, "round_up_quantum": 4096}},
        "current_workload_targets": {"cpu_seconds": 0.3, "peak_rss_kib": 65536},
        "interpretation": [
            "Existing coefficients and charged-work points are unchanged; the CPU point has an empirical minimum.",
            "Review thresholds are deliberately loose decision allowances, not typical predictions or calibrated bounds.",
            "The separately chosen current-workload targets never clamp the formula thresholds.",
            "Acceptance requires actual measured CPU and RSS medians and maxima inside both allowances and targets.",
            "Feature ranges are only scope checks; unmeasured combinations inside them have not been validated.",
            "No optimizer, compiler refusal limit, production stopping policy or automatic limit adjustment is implied."]}
    return result


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
    calibration = model.get("decision_support_calibration")
    for name, result in model["responses"].items():
        ready = "coefficients" in result and result["status"] != "not-converged"
        responses[name] = {"units": result["units"], "status": "point-estimate" if ready else result["status"],
                           "predicted": point(result["coefficients"], vector) if ready else None}
        if calibration:
            response = responses[name]
            response["role"] = "physical-cost" if name in PHYSICAL else "diagnostic-only"
            if name in PHYSICAL and ready:
                response["raw_predicted"] = response["predicted"]
                if name == "cpu_seconds":
                    response["predicted"] = max(response["predicted"], calibration["cpu_point_floor_seconds"])
                policy = calibration["review_thresholds"][name]
                response["review_threshold"] = round_up(policy["multiplier"] * response["predicted"] + policy["offset"],
                                                        policy["round_up_quantum"])
                response["current_workload_target"] = calibration["current_workload_targets"][name]
    return {"features": vector, "outside_observed_ranges": outside, "responses": responses,
            "interpretation": ("Physical points and separate review allowances; acceptance requires actual measurements. "
                               "Unmeasured combinations are not validated, even inside feature ranges. "
                               "Charged work is diagnostic only; no refusal limit or optimizer decision is implied."
                               if calibration else "Rough typical-cost prediction, not an admission allowance or limit adjustment.")}


def decision(case, estimated):
    physical, reasons = {}, []
    if estimated["outside_observed_ranges"]:
        reasons.append("outside-observed-feature-ranges")
    for name in PHYSICAL:
        predicted = estimated["responses"].get(name, {})
        observed = observation(case, name) or {}
        median, maximum = observed.get("median"), observed.get("max")
        valid = (collector.numeric(median) and collector.numeric(maximum) and 0 <= median <= maximum
                 and collector.numeric(observed.get("n")) and observed["n"] >= 3)
        ready = predicted.get("review_threshold") is not None and predicted.get("current_workload_target") is not None
        physical[name] = {**predicted, "observed_median": median, "observed_maximum": maximum,
                          "measurement_count": observed.get("n")}
        if not valid or not ready:
            reasons.append("missing-or-invalid-measured-" + name)
            continue
        physical[name].update({"median_within_review_threshold": median <= predicted["review_threshold"],
                              "maximum_within_review_threshold": maximum <= predicted["review_threshold"],
                              "median_within_current_target": median <= predicted["current_workload_target"],
                              "maximum_within_current_target": maximum <= predicted["current_workload_target"]})
    within = all(value.get("maximum_within_review_threshold") and value.get("maximum_within_current_target")
                 for value in physical.values())
    return {"case": case["id"], "status": ("outside-calibration" if reasons else
                                           "acceptable-for-current-decision" if within else "review-needed"),
            "scope_reasons": reasons, "outside_observed_ranges": estimated["outside_observed_ranges"],
            "responses": physical}


def evaluate(model, summary):
    rows = {name: [] for name in RESPONSES}
    excluded, decisions = [], []
    for case in summary["cases"]:
        if not case.get("accepted_for_models"):
            excluded.append(case["id"])
            continue
        estimated = prediction(model, case)
        if model.get("decision_support_calibration"):
            decisions.append(decision(case, estimated))
        for name, result in estimated["responses"].items():
            observed = actual(case, name)
            if result["predicted"] is not None and collector.numeric(observed):
                rows[name].append({"case": case["id"], "actual": observed, "predicted": result["predicted"],
                                   "outside_observed_ranges": estimated["outside_observed_ranges"]})
    result = {"interpretation": "Descriptive comparison with existing examined evidence; no refitting and no claim of blind validation.",
              "excluded_case_ids": excluded, "responses": {name: errors(values) for name, values in rows.items()}}
    if model.get("decision_support_calibration"):
        result["decision_support"] = {
            "interpretation": "Current measured cases only; feature ranges do not validate unmeasured combinations. "
                              "Review-needed requests investigation, not automatic optimization or compiler refusal.",
            "status_counts": {status: sum(row["status"] == status for row in decisions) for status in
                              ("acceptable-for-current-decision", "review-needed", "outside-calibration")},
            "cases": decisions}
    return result


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
    physical_cases = json.loads(json.dumps(cases))
    for case in physical_cases:
        value = actual(case, "cpu_seconds")
        case["process"]["off"] = {
            "wrapper_inclusive_child_total_seconds": {"median": value / 10000, "max": value / 10000 + 0.001, "n": 3},
            "peak_rss_kib": {"median": 12000 + value * 20, "max": 12100 + value * 20, "n": 3}}
    physical_model = fit_summary({"cases": physical_cases})
    startup = {"complete": True, "cases": [{"id": "flat-width0", "controlled_complete": True, "issues": [],
                "language_metrics": {"ash": {"wrapper_child_total_seconds": {"median": 0.009199, "n": 3}}}}]}
    calibrated = calibrate(physical_model, startup, "base-hash", "startup-hash")
    assert calibrated["decision_support_calibration"]["cpu_point_floor_seconds"] == 0.01
    assert calibrated["responses"] == physical_model["responses"]
    estimated = prediction(calibrated, physical_cases[0])
    cpu = estimated["responses"]["cpu_seconds"]
    assert cpu["raw_predicted"] < cpu["predicted"] == 0.01
    assert cpu["review_threshold"] >= 2 * cpu["predicted"] + 0.01
    assert estimated["responses"]["source-checking"]["role"] == "diagnostic-only"
    assert estimated["responses"]["source-checking"]["predicted"] == prediction(physical_model, physical_cases[0])["responses"]["source-checking"]["predicted"]
    checked = evaluate(calibrated, {"cases": physical_cases})
    assert checked["decision_support"]["status_counts"]["acceptable-for-current-decision"] == len(physical_cases)
    physical_cases[0]["process"]["off"]["wrapper_inclusive_child_total_seconds"]["max"] = 0.031
    physical_cases[1]["features"]["nodes"] = calibrated["feature_ranges"]["nodes"]["max"] + 1
    physical_cases[2]["process"]["off"]["peak_rss_kib"]["max"] = None
    checked = evaluate(calibrated, {"cases": physical_cases})
    assert checked["decision_support"]["cases"][0]["status"] == "review-needed"
    assert checked["decision_support"]["cases"][0]["responses"]["cpu_seconds"]["median_within_review_threshold"]
    assert checked["decision_support"]["cases"][0]["responses"]["cpu_seconds"]["maximum_within_current_target"]
    assert checked["decision_support"]["cases"][1]["status"] == "outside-calibration"
    assert checked["decision_support"]["cases"][2]["status"] == "outside-calibration"
    large = prediction(calibrated, {"nodes": 40000, "type_nodes": 1, "type_depth": 1, "resource_sites": 0})
    assert large["responses"]["cpu_seconds"]["review_threshold"] > large["responses"]["cpu_seconds"]["current_workload_target"]
    for case in cases:
        case["features"] = {"nodes": 1, "type_nodes": 1, "type_depth": 1, "resource_sites": 0}
    failed = fit_summary({"cases": cases})
    assert failed["responses"]["cpu_seconds"]["status"] == "rank-insufficient"
    assert prediction(failed, cases[0])["responses"]["cpu_seconds"]["predicted"] is None
    print("Connected offline fit, calibration, prediction, measured review and scope self-check passed.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    command = commands.add_parser("fit"); command.add_argument("summary", type=Path); command.add_argument("--output", type=Path, required=True)
    command = commands.add_parser("calibrate"); command.add_argument("model", type=Path); command.add_argument("startup_summary", type=Path); command.add_argument("--output", type=Path, required=True)
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
    elif args.command == "calibrate":
        if args.output.resolve() in (args.model.resolve(), args.startup_summary.resolve()):
            raise ValueError("calibration output must preserve the base model and startup evidence")
        model = calibrate(json.loads(args.model.read_text()), json.loads(args.startup_summary.read_text()),
                          collector.sha(args.model), collector.sha(args.startup_summary))
        model["decision_support_calibration"]["provenance"].update(
            base_model_path=str(args.model.resolve()), startup_summary_path=str(args.startup_summary.resolve()))
        collector.dump(args.output, model)
        print(json.dumps({"output": str(args.output), "cpu_point_floor_seconds": model["decision_support_calibration"]["cpu_point_floor_seconds"],
                          "interpretation": "No refit; physical review allowances and current-workload targets remain separate."}, indent=2))
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
