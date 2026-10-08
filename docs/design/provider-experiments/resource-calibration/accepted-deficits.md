# Adopted calibration with accepted deficits, 2026-10-08

This is the offline adoption of the user's calibrated decision-support
measurements under [TASK-0035](../../../tasks/TASK-0035-resource-analysis-relevance-and-fusion.md)
and [DN-0036](../../DN-0036-foreign-library-and-memory-provider-experiments.md).
Common coordinates the separate compiler admission work. This checkpoint
changes no Rust source, compiler limit or integration state and runs no
compiler engine.

The [adopted model](adopted-decision-model.json) preserves the entire
[previous calibration](decision-budget-model.json), including coefficients,
point predictions, feature ranges, review thresholds and current-workload
targets. It adds an explicit **at-most-10% accepted deficit**, with provenance
pointing to the preserved parent artifact. Previous evidence is unchanged.

## Assessment rule

For each measured CPU/RSS median and observed maximum, compare the observation
with **both** its original review threshold and current-workload target:

```text
absolute deficit = observed - original baseline
relative deficit = absolute deficit / original baseline
future optimization target = original baseline
required reduction fraction = absolute deficit / observed
```

A deficit exists only when observed cost exceeds that baseline. Classify the
completed case as follows:

| Outcome | Meaning |
| --- | --- |
| `acceptable-for-current-decision` | Every applicable observation is inside its original baselines. |
| `accepted-with-deficit` | At least one baseline is exceeded, and every excess is at most 10% of its own original baseline. Record the deficits as future optimization targets; they do not block continued work. |
| `review-needed` | At least one excess is greater than 10% of its original baseline. |
| `outside-calibration` | Measurements or prediction inputs are missing/invalid, or the descriptors are outside the retained ranges. This takes precedence over deficit acceptance. |

The denominator is always the original exceeded baseline. Allowances do not
compound, and adopting an already adopted model cannot enlarge them. Exact
rational comparisons of reported decimal numeric values include the 10%
boundary without an epsilon. Every known excess remains reportable even if
another missing observation or scope failure prevents acceptance.

Each deficit records the measure and units, median/maximum statistic, baseline
name and value, observed value, absolute and relative deficit, original
optimization target, required absolute reduction and reduction relative to
observed cost. A 10% deficit relative to the baseline requires a **9.09%**
reduction in observed cost to meet it. The point-prediction residual remains
a separate diagnostic; the 10% rule applies to review thresholds and targets.

For example, these are synthetic boundary examples, not new measurements:

| Baseline | Observed | Deficit relative to baseline | Outcome / future target |
| --- | ---: | ---: | --- |
| CPU review threshold 220 ms | 242 ms | 22 ms / 10% | Accepted with deficit; target 220 ms. |
| CPU target 300 ms | 330 ms | 30 ms / 10% | Accepted with deficit if every other baseline also fits; target 300 ms. |
| CPU review threshold 370 ms and target 300 ms | 400 ms | 8.11% and 33.33% | Review required; the acceptable review-threshold deficit cannot hide the larger target deficit. |

Future targets are reported data. The tool does not schedule optimization or
change compiler stopping policy. Out-of-range results do not become accepted
because their physical costs happen to fit a tolerance.

## Completed replay and boundary evidence

The [primary replay](adopted-decision-evaluation.json) reports **52 acceptable
cases, zero accepted deficits, zero review cases and zero outside cases**.
These existing observations already met the original baselines, so this
adoption invents no current optimization deficit.

The [structural reference replay](adopted-decision-reference-evaluation.json)
retains **nine acceptable cases and five outside calibration**, with no
deficits. Nine reference IDs overlap the primary set; these are separate
replays of examined evidence, not 66 independent programs or blind validation.
All earlier observations and prediction residuals remain unchanged.

The connected offline self-check exercises fit, calibration, adoption and
assessment. The separately indexed [synthetic boundaries](accepted-deficit-boundaries.json)
record **30 evaluator replays**: eight acceptable, nine accepted with deficit,
ten requiring review and three outside calibration. They cover CPU and RSS,
both baseline classes, median-and-maximum and maximum-only excess at zero,
exactly 10% and above 10%; multiple baselines; missing observations; and
scope/feature failures. Test-only constant point overrides isolate each
baseline and never modify the adopted model or recorded measurements.

The exact mathematical RSS target ceiling is 72,089.6 KiB for a 65,536 KiB
baseline. The integral-KiB controls accept 72,089 KiB and require review at
72,090 KiB. Fractional-KiB synthetic boundaries test arithmetic and are not
presented as GNU time observations. Replaying old models still gives exact
JSON-value equality with both prior evaluation artifacts.

## Independent charged-work budget review

The [read-only work-budget review](work-budget-review.json) recommends the
following independently measured references for Common's admission work:

| Measured primary owner | Completed maximum, charged units | Rounded nominal budget | Separate 10% hard ceiling |
| --- | ---: | ---: | ---: |
| Structural Type | 1,212,707 | 1,300,000 | 1,430,000 |
| Independent Core | 1,609,087 | 1,700,000 | 1,870,000 |

These are recommendations, not compiler changes in this checkpoint. The
100,000-unit upward rounding is explicit headroom. The additional 10% margin
is relative to the rounded nominal budget, not the observed maximum. Therefore
the proposed ceilings are 17.92% and 16.21% above the measured maxima. For a
generic integer budget, `budget + budget / 10` keeps the margin at most 10%
without rounding its fraction upward. No CPU or RSS value is converted into
charged units, and cumulative module endpoints are never summed as independent
work.

Coverage is limited to the measured primary owners. The builder's separate
construction and rewrite owners ([dialect.rs](../../../../src/core/dialect.rs))
are not recorded by the six phase endpoints; final elaboration emits the
elaborator's endpoint before builder completion
([elaborate.rs](../../../../src/elaborate.rs)). These measurements cannot alone
prove completion under revised ordinary limits.

The retained validator derives its Core limit as three times the shared Type
limit ([validate.rs](../../../../src/core/validate.rs)). Installing 1,430,000
as that shared hard limit without decoupling would give Core 4,290,000 units,
rather than the proposed independent 1,870,000. The validator, ratio-based
diagnostic override ([calibration.rs](../../../../src/calibration.rs)) and
driver phase labels need consistent treatment. Constraint, usefulness,
runtime and unreported builder owners remain separate. Current normative
[ledger ownership](../../../../spec/static-semantics.md#failure-ownership-and-constraint-resources)
also keeps Core construction and validation separate.

Common owns any production adoption, ordinary-limit executable verification
and its serial Cargo window. This worktree provides the review and evidence
without building, merging, integrating or changing stopping policy.

## Evidence and reproduction

[The adoption evidence index](accepted-deficit-evidence.json) authenticates the
new model, replays, boundary cases, work-budget review and verification receipt.
It also pins previous artifacts without modifying them. The original
[52-case inputs](decision-budget-inputs.json) and
[14-case reference inputs](decision-budget-reference-inputs.json) are reused.

From the calibration worktree:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tools/resource_budget_estimates.py self-check
PYTHONDONTWRITEBYTECODE=1 python3 tools/resource_budget_estimates.py adopt docs/design/provider-experiments/resource-calibration/decision-budget-model.json --output NEW_ADOPTED_MODEL.json
PYTHONDONTWRITEBYTECODE=1 python3 tools/resource_budget_estimates.py evaluate NEW_ADOPTED_MODEL.json docs/design/provider-experiments/resource-calibration/decision-budget-inputs.json
PYTHONDONTWRITEBYTECODE=1 python3 tools/resource_budget_estimates.py evaluate NEW_ADOPTED_MODEL.json docs/design/provider-experiments/resource-calibration/decision-budget-reference-inputs.json
```

To replay the synthetic artifact, load its `cases`; for each case, copy the
adopted model, replace only the declared test-only constant point coefficients,
then call `evaluate` on its `input_case`. Compare the returned case record
with `result` and `expected_status`. The artifact retains every test input,
override and output; the actual model remains unchanged.

This remains retrospective, host-specific decision support. The previous
calibration's program-size, complexity, measurement and validation boundaries
continue to apply.
