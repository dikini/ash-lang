# Local retained-control model

These bounded C1 ownership and C3 drain models support
[DN-0056](../DN-0056-scoped-continuation-retention-and-library-scheduling.md)
and [CP-0026](../../proposals/CP-0026-scoped-owned-continuation-storage.md).
They do not define current Ash. The [C1 correspondence map](correspondence.md)
states its premises, proved claims and unproved product obligations.

| Module | Scope |
| --- | --- |
| [Ownership](Ownership.lean) | Finite owner inventories, transfer and restore transitions, completion, support, generations and failure accounting. |
| [OwnershipExamples](OwnershipExamples.lean) | Concrete positive and negative traces over those transitions. |
| [DrainSafety](DrainSafety.lean) | Finite focused-State normal returns, port cases and the checked Store-close predecessor. |

The C1 candidate passed independent source review and a frozen scoped
[AD-0012](../../decisions/AD-0012-proof-development-feedback-and-build-reuse.md)
integration build. The [gate record](../../tasks/evidence/local-retained-control/c1-model/README.md)
pins its sources, compiler, review and reports. CP-0026 is accepted, and C1's
retained result was independently verified; the [active task](../../tasks/TASK-0057-local-retained-control.md)
tracks the remaining implementation and gates.

The C3 [drain correspondence](drain-correspondence.md) records the concrete
control, value and completion premises used by the bounded analysis. Its
reviewed source completed a separate frozen [gate](../../tasks/evidence/local-retained-control/c3-model/README.md);
its receipt passed independent audit. Connected public validation remains open.
