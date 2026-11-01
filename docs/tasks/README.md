# Tasks

Tasks plan and record active implementation work authorized by an accepted
change proposal or architectural decision. They may record dependencies, work,
progress, verification, discoveries, and deviations. They never define
language semantics.

Use [the template](template.md) and allocate the next `TASK-NNNN` ID.

## Active tasks

- [TASK-0063: Host-default Store close](TASK-0063-host-default-store-close.md)
  tracks the first case in [issue #165](https://github.com/dikini/ash-lang/issues/165).
- [TASK-0062: Verified Module Reuse](TASK-0062-verified-module-reuse.md) tracks
  the compiler pipeline change in [issue #201](https://github.com/dikini/ash-lang/issues/201).
- [TASK-0060: Frame Composition Work](TASK-0060-frame-composition-work.md) tracks
  the capacity repair for [issue #196](https://github.com/dikini/ash-lang/issues/196).
- [TASK-0059: Nested Cell Validation](TASK-0059-nested-cell-validation.md) tracks
  the correction for [issue #195](https://github.com/dikini/ash-lang/issues/195).

The retained-control [specification](../../spec/README.md) and
[bounded evidence](../design/retained-control/README.md) are integrated on
Main through [PR #167](https://github.com/dikini/ash-lang/pull/167) at
`67c79ddc32a813cc0c9ddab2962f9e2aa849b028`. The C5 and Main handoffs are
complete. [Issue #165](https://github.com/dikini/ash-lang/issues/165) records
two analysis limitations without adding language restrictions.

The lexical-region product's language rules are in the
[specification](../../spec/README.md); its existing
[model evidence](../design/lexical-regions/evidence.md) retains the bounded proof
scope. [R5 #70](https://github.com/dikini/ash-lang/issues/70) records product
acceptance. The lexical-region implementation is integrated into Main through
[PR #157](https://github.com/dikini/ash-lang/pull/157).

[TASK-0053](https://github.com/dikini/ash-lang/blob/2766e8260e2590d9ebdca7abd699115b3cd02a8a/docs/tasks/TASK-0053-checked-owner-core-execution.md) and
[TASK-0054](https://github.com/dikini/ash-lang/blob/2766e8260e2590d9ebdca7abd699115b3cd02a8a/docs/tasks/TASK-0054-checked-sqlite-source-policy.md) are superseded
assignments, not completed delivery gates. Their history remains in Git.

The generic cell product checkpoint is integrated into local `main`. Its
[case map, verification and local history](../design/generic-cell/evidence.md)
record the completed transition, Main integration and exact scope.
[DN-0054](../design/DN-0054-base-lexical-region-memory-contracts.md)
retains informative questions about broader ownership and reclamation schemes.

## Historical source/static work

[TASK-0051: Checked FFI Contract Carriers](https://github.com/dikini/ash-lang/blob/2766e8260e2590d9ebdca7abd699115b3cd02a8a/docs/tasks/TASK-0051-checked-ffi-contract-carriers.md)
records the original F3 source/summary/Core/private-image work. That checked-host
programme is superseded and its specialized execution routes are retired. The
[obligation map](evidence/checked-ffi-original-acceptance/README.md) retains the
historical acceptance scope; it is not current product functionality.

## Historical ffi-ash closure coordination

The [original issue #7 handoff](https://github.com/dikini/ash-lang/issues/7#issuecomment-6234064548)
and [TASK-0041 history](https://github.com/dikini/ash-lang/blob/7471200efb1bd90782fcad81be54b992fbd92982/docs/tasks/TASK-0041-ffi-ash-milestone-closure.md)
retain the earlier foreign-policy milestone's coordination and acceptance
record. The accepted current `ffi-ash` scope is recorded in
[DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md) and the
[feature inventory](../project/implemented-features.md). The original library
and checked-host assignments are not active requirements of that current scope.

The [TASK-0042 performance record](../project/verification-performance-2026-10-20.md)
retains the completed controlled comparison and tooling findings. Its completed
task and execution plan are retired.
