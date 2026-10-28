# Local retained-control model

This is a candidate bounded C1 model for the [DN-0056 assignment](../DN-0056-scoped-continuation-retention-and-library-scheduling.md#c1-bounded-ownership-and-completion-proof-assignment)
and [CP-0026](../../proposals/CP-0026-scoped-owned-continuation-storage.md).
It does not define current Ash. The [correspondence map](correspondence.md)
states the premises, proved claims and unproved product obligations.

| Module | Scope |
| --- | --- |
| [Ownership](Ownership.lean) | Finite owner inventories, transfer and restore transitions, completion, support, generations and failure accounting. |
| [OwnershipExamples](OwnershipExamples.lean) | Concrete positive and negative traces over those transitions. |

The local compiler checks are development feedback only. Independent review
and the frozen scoped [AD-0012](../../decisions/AD-0012-proof-development-feedback-and-build-reuse.md)
integration gate are pending until their exact source, compiler, review and
report receipts are recorded. No product implementation follows from this
candidate alone.
