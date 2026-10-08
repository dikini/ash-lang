# Calibration observer integration

This tooling reconciliation follows the [TASK-0035 disposition](../analysis-closure.md)
and preserves the historical calibration evidence and
Common's separately selected public phase allowances. It remains part of the
bounded [DN-0036](../../DN-0036-foreign-library-and-memory-provider-experiments.md)
experiment; it defines no Ash semantics or general compiler admission
architecture.

The original reports, archives, manifests, coefficients and executable hashes
describe their recorded revisions. Keep their bytes unchanged. A reconciled
executable is a new measurement identity and requires a new manifest and output
directory, even when the Ash input text is unchanged.

The observer records `normal_limit` as the ordinary selected hard stopping
allowance and `diagnostic_limit` as the actual effective ledger capacity. The
nominal prediction is separate from both. With no explicit diagnostic override,
these two recorded capacities agree. Public Source, final-elaboration and Core
hard allowances are respectively 1,369,702, 432,537 and 1,802,240 charged units.
Standalone Type and Core defaults remain 327,680 and 983,040.

With `resource-calibration` enabled, `ASH_CALIBRATION_LIMIT` explicitly selects
a finite diagnostic base between 1 and 268,435,456. Structural and constraint
owners receive that base; independent Core receives three times the base.
These are measurement conventions, not ratios inferred from the ordinary
allowances. Observation ON and OFF must use the same effective capacities.
Without the feature, the environment variables have no effect. With the
feature but without a diagnostic override, ordinary admission remains selected.

Only complete owner creation selects an override. Exact caller allowances,
remaining sub-budgets, builder/rewrite capacities and other uninstrumented
owners keep their existing accounting. A diagnostic completion above an
ordinary allowance does not establish ordinary admission.

Each successful measured owner emits one final work record. Per-module Source
phase endpoints remain cumulative diagnostics and must not be summed. Failed
phases retain incomplete timing records; Common's public failure report retains
the measured partial work. Final-elaboration completion follows successful
`finish_with_work`, including builder finishing. There is no duplicate inner
final-elaboration endpoint.

The generated native measurement test is ignored during ordinary test runs
because it requires an explicit input and session count. To run an already-built
feature-enabled harness, use a new generated input and request the ignored test
explicitly:

```sh
ASH_CALIBRATION_ENTRY=/absolute/new-inputs/resource-width-1.ash \
ASH_CALIBRATION_SESSIONS=1 \
ASH_CALIBRATION_LIMIT=16777216 \
ASH_CALIBRATION_OBSERVE=1 \
/absolute/new-build/resource_calibration_native \
  generated_resource_sessions_close_every_connection \
  --exact --ignored --test-threads=1 --nocapture
```

The input must be produced by the resource-width generator; the session count
must match it. New manifests produced by `resource_calibration_cases.py generate`
add `--ignored` only to this generated native harness. Ordinary copying,
session and control tests remain ordinary test selections. Preserve historical
manifests; they retain the old harness contract and pinned executable identity.

Builds and measurements remain separate. Common owns the serial compiler window
and integration validation. An ordinary full verification run must not receive
`ASH_CALIBRATION_LIMIT`. The process-level observer regression checks Pure and
Effect paths with observation ON/OFF, ordinary and explicit diagnostic
capacities, one endpoint per owner, and an incomplete Source rejection.
