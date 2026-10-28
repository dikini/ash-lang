# C3 bounded drain proof gate record

This record belongs to [TASK-0057](../../../TASK-0057-local-retained-control.md).
It covers the bounded normal-return and drain analysis and its reviewed
implementation correspondence. It does not establish public Store admission,
the complete C2/C3 implementation, or current language semantics.

The independently reviewed [source and correspondence](review.md) are pinned
by [review.json](review.json) and [reviewed-manifest.json](reviewed-manifest.json)
at product checkpoint `0f73745eeb897c9018638a210aa34c26ca53de9c`. The exact
reviewed correspondence is preserved in [reviewed-correspondence.md](reviewed-correspondence.md);
the current [proof root](../../../../design/retained-control/README.md) links
its maintained map and model.

The frozen integration used [config.json](config.json) and the unchanged
[C1 evidence](../c1-model/evidence.json). The [evidence.json](evidence.json)
has SHA-256
`717fea322b63c90626938c0c98fadf3cbb2f4735a41959542fb1003ebafb3a90`.
Lean 4.33.1 compiled DrainSafety with one job and warnings as errors;
the unchanged Ownership and OwnershipExamples artifacts were reused. The
[gate log](gate.log) records 82 reports: 18 and 31 retained C1 reports, and
33 new reports in [DrainSafety.log](DrainSafety.log). All use only the
standard permitted axioms. The [manifest](manifest.json) and
[module progress](module-progress.json) record the exact source, artifact and
scheduler pins. The independent [receipt audit](audit.md) and its
[checks](audit-checks.json) verified the frozen result.

The first runner attempt stopped before compilation because the sandbox could
not write the canonical host lock. The successful retry used the same reviewed
inputs and host-wide lock with a fresh output prefix. The copied configuration
and receipt preserve their original bytes and absolute run paths; those paths
identify the run and are not portable links. Compiled artifacts remain in the
shared module cache. The real linked release check, full-pipeline budget,
transformed and executable cases, and the connected C2/C3 checkpoint remain
separate obligations.
