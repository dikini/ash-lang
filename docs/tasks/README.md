# Tasks

Tasks plan and record active implementation work authorized by an accepted
change proposal or architectural decision. They may record dependencies, work,
progress, verification, discoveries, and deviations. They never define
language semantics.

Use [the template](template.md) and allocate the next `TASK-NNNN` ID.

## Active tasks

The following tasks implement the accepted
[CP-0023](../proposals/CP-0023-scoped-generic-cells.md) transition after ash-ffi.
Implementation has not started. TASK-0049 owns the case map, readiness handoffs
and complete checkpoint; the other tasks own bounded implementation and evidence.

| Task | Work | Readiness dependency |
| --- | --- | --- |
| [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md) | Generic Cell API, acquisition typing and authenticated Core foundation | Pinned ash-ffi product base and accepted CP-0023 |
| [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | Contents flow, captures, strict dependencies and independent Core checking | Reviewed TASK-0045 foundation |
| [TASK-0047](TASK-0047-generic-cell-execution-and-completion.md) | Payload execution, handlers and structural completion | Reviewed TASK-0045 foundation; TASK-0046 checking before public admission |
| [TASK-0048](TASK-0048-generic-cell-integrated-verification.md) | Integrated validation, budgets and ash-ffi compatibility | Connected TASK-0045–0047 implementation |
| [TASK-0049](TASK-0049-close-generic-cell-checkpoint.md) | Specification, complete acceptance and product checkpoint | Evidence from all four implementation tasks |

Readiness permits dependent work; it does not mark a task's acceptance complete.
All 31 proposal cases remain unchecked until their full observations are
established. [DN-0054](../design/DN-0054-base-lexical-region-memory-contracts.md)
remains separate design work and is neither an implementation task nor a
dependency of this checkpoint.
