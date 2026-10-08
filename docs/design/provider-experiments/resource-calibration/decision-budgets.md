# Provisional decision budgets, 2026-10-08

This records the user's acceptance of current measured costs for continued
feature development under [TASK-0035](../../../tasks/TASK-0035-resource-analysis-relevance-and-fusion.md)
and [DN-0036](../../DN-0036-foreign-library-and-memory-provider-experiments.md).
The calibrated offline assessment accepts all **52 primary measured cases**,
including the five realistic SQLite witnesses. **No further optimization is
required by these measurements.** Production compiler stopping limits remain
unchanged; this is decision support for the retained experimental baseline.

## Predictions, observations and decisions

The [original four-term model](rough-budget-model.json) remains unchanged:

```text
raw prediction = a + b*surface_nodes
                   + c*(type_nodes*type_depth)
                   + d*(resource_sites*surface_nodes)

CPU point prediction = max(raw CPU prediction, 10 ms)
RSS point prediction = raw RSS prediction

CPU review threshold = round_up(2*CPU point prediction + 10 ms, 10 ms)
RSS review threshold = round_up(1.5*RSS point prediction, 4 MiB)
```

The [calibrated artifact](decision-budget-model.json) retains every original
coefficient and charged-unit prediction. The CPU floor rounds the measured
zero-width control's 9.199 ms median up to the next 5 ms, giving 10 ms.
This complete small-program control is not a universal startup lower bound.
The floor prevents implausibly tiny predictions without adding startup to
an already fitted whole-process total. Peak RSS already has a fitted fixed
cost, so its point prediction needs no additional floor.

These quantities have different roles:

| Quantity | Role |
| --- | --- |
| Point prediction, or budget | Rough expected typical cost for the supplied size/complexity descriptors. |
| Observation | Measured CPU, process peak RSS or separately charged units; each retains its own units. |
| Review threshold | A deliberately loose tolerance for deciding whether to investigate a prediction miss. It is not a prediction or statistical confidence bound. |
| Current-workload target | A chosen engineering objective of **300 ms CPU and 64 MiB peak RSS** for the current workload set on this host. |
| Compiler stopping limit | A separate admission policy; this batch changes none of its constants or behavior. |

The threshold multipliers, rounding and engineering targets are pragmatic
choices made after examining the evidence. They are not estimates of a
universal maximum. Formula thresholds and targets remain separate: persistence
has a 370 ms CPU review threshold and a 300 ms engineering target. Neither is
silently substituted for the other.

An assessment reports `acceptable-for-current-decision` only when completed
CPU and RSS observations have at least three measurements, both medians and
observed maxima meet their review thresholds and targets, and descriptors
lie inside the original model's feature ranges. Prediction alone cannot
accept an unmeasured program. New combinations remain unvalidated even when
each individual descriptor lies inside those ranges.

## Current SQLite results

CPU values below are milliseconds. Measured memory is the median process
peak RSS; the review column gives the separate memory threshold.
All five cases meet both their thresholds and the common engineering targets.

| Case | CPU prediction | CPU median / observed maximum | CPU review threshold | RSS median / review threshold, MiB |
| --- | ---: | ---: | ---: | ---: |
| Copying | 104.9 | 183.7 / 214.6 | 220 | 33.57 / 40 |
| Persistence | 175.3 | 229.5 / 259.2 | 370 | 42.38 / 56 |
| Resume | 86.5 | 62.1 / 65.8 | 190 | 22.54 / 36 |
| Bound NUL | 104.9 | 182.2 / 184.4 | 220 | 33.50 / 40 |
| Forwarding | 84.6 | 63.6 / 65.3 | 180 | 22.15 / 36 |

The largest measured CPU value is 259.204 ms and the largest peak RSS is
42.5625 MiB, both from persistence. Copying still costs approximately 1.75
times its point CPU prediction, and its Source charge estimate still misses
1,212,707 charged units against a prediction near 476,786. Those misses are
visible; the decision accepts their modest physical cost rather than claiming
a more accurate model or demanding an optimization.

Charged-unit predictions remain diagnostic. Charges include reservations and
are not executed instruction counts. Their ratios alone do not determine
whether optimization is required. CPU and RSS are measured separately and
are not converted into charged units.

The original whole-pipeline Ash measurements used the finite experimental
diagnostic allowance, with the ordinary limits unchanged. Acceptable physical
cost does not establish admission under ordinary production limits. Any
production admission-policy change remains separate work; these results do
not require optimization as its prerequisite.

## Coverage and retained uncertainty

The [primary replay](decision-budget-evaluation.json) assesses all 44 original
CPU-precision cases and eight previously examined language fixtures. All 52
meet both the physical review thresholds and targets, including their observed
maxima. This is explicit recalibration on examined data, not blind validation.
The fitted coefficients were not refitted, and repetitions are not additional
independent programs.

The CPU floor reduces RMSE on the original 44 cases from 26.30 to 26.09 ms,
and on the eight basic fixtures from 6.40 to 2.96 ms. The combined 52-case CPU
RMSE is 24.03 ms; RSS RMSE remains 2.73 MiB. These absolute errors describe
this evidence, not predicted accuracy for arbitrary programs. The model still
overpredicts several structural examples and underpredicts copying.

The [14-case structural cross-check](decision-budget-reference-evaluation.json)
also meets all physical thresholds and targets. Nine IDs overlap the primary
set; the cross-check is kept separate rather than counted as additional
independent programs. Nine reference cases are inside the original feature
ranges; five retain `outside-calibration` status: the
zero-width startup control and type/prerequisite depths 24 and 32. Their
measured costs are acceptable, but their features do not become validated
interpolation merely because their costs fit a loose tolerance. No feature
range was expanded to hide these flags.

These targets concern the current workload set and host: Linux x86-64,
AMD Ryzen 7 7435HS, optimized Ash builds, fixed native dependencies and the
recorded measurement boundary. Larger programs, different type/effect/resource
compositions, another host or another compiler version need new measurements
and an explicit reassessment. Target wall time remains observational because
scheduling and I/O can add delays independently of CPU cost.

## How to use the result

Continue feature development on this baseline. Compare a completed program's
actual CPU and peak RSS with its point predictions, review thresholds and
stated workload targets. Keep prediction residuals visible. An assessment
outside tolerance requests review of measurement noise, workload changes,
model scope and physical cost; it does not automatically require optimization.
Consider optimization when repeated measurements establish a material
practical problem, rather than from a charged-unit miss alone.

A missing measurement or an out-of-range descriptor reports
`outside-calibration`. Choose a new workload target explicitly when the
program size or complexity changes; the current 300 ms / 64 MiB targets do
not become universal compiler limits. The tool does not run the compiler,
change allowances, refuse programs or schedule optimization.

## Evidence and reproduction

[The evidence index](decision-budget-evidence.json) authenticates the derived
input snapshots, model, replay, tool and verification receipt. The
[52-case input snapshot](decision-budget-inputs.json),
[startup control](decision-budget-startup.json) and
[structural reference snapshot](decision-budget-reference-inputs.json)
preserve their source-summary hashes. The original measurements, old model
and previous evidence indexes remain unchanged.

The connected offline self-check exercises fit, calibration, prediction and
measured assessment together, including a maximum-only overrun, a missing
observation and an outside-range case. Stored-data replay supplies the real
integration check. This batch ran no Ash, Rust, Cargo or C compiler process
and required no compiler window.

From this worktree, reproduce with the preserved inputs:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tools/resource_budget_estimates.py self-check
PYTHONDONTWRITEBYTECODE=1 python3 tools/resource_budget_estimates.py calibrate docs/design/provider-experiments/resource-calibration/rough-budget-model.json docs/design/provider-experiments/resource-calibration/decision-budget-startup.json --output NEW_MODEL.json
PYTHONDONTWRITEBYTECODE=1 python3 tools/resource_budget_estimates.py evaluate NEW_MODEL.json docs/design/provider-experiments/resource-calibration/decision-budget-inputs.json
PYTHONDONTWRITEBYTECODE=1 python3 tools/resource_budget_estimates.py evaluate NEW_MODEL.json docs/design/provider-experiments/resource-calibration/decision-budget-reference-inputs.json
```

`predict MODEL FEATURES_JSON` reports raw and calibrated points, separate
thresholds and targets. It requires the same four raw descriptors as the
original estimator. It does not report acceptance without actual observations.
Local absolute paths identify historical inputs; relocate them for reproduction
and retain the original evidence hashes.
