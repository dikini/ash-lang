# Local retained-control model

This is a candidate bounded C1 model for the [DN-0056 assignment](../DN-0056-scoped-continuation-retention-and-library-scheduling.md#c1-bounded-ownership-and-completion-proof-assignment)
and [CP-0026](../../proposals/CP-0026-scoped-owned-continuation-storage.md).
It does not define current Ash. The [correspondence map](correspondence.md)
states the premises, proved claims and unproved product obligations.

| Module | Scope |
| --- | --- |
| [Ownership](Ownership.lean) | Finite owner inventories, transfer and restore transitions, completion, support, generations and failure accounting. |
| [OwnershipExamples](OwnershipExamples.lean) | Concrete positive and negative traces over those transitions. |

The candidate passed independent source review and a frozen scoped
[AD-0012](../../decisions/AD-0012-proof-development-feedback-and-build-reuse.md)
integration build. The [gate record](../../tasks/evidence/local-retained-control/c1-model/README.md)
pins its sources, compiler, review and reports. CP-0026 is accepted;
retained-result verification remains separate before C2 product work starts.
