# Tasks

Tasks plan and record active implementation work authorized by an accepted
change proposal or architectural decision. They may record dependencies, work,
progress, verification, discoveries, and deviations. They never define
language semantics.

Use [the template](template.md) and allocate the next `TASK-NNNN` ID.

## Active tasks

  measures and repairs issue #91 under unchanged defaults and independent
  source/owner/Core admission.

- [TASK-0051: Checked FFI Contract Carriers](TASK-0051-checked-ffi-contract-carriers.md)
  implements F3 under accepted CP-0024; source/summary/Core/image acceptance remains
  pending until the complete carrier boundary is independently verified.

- [TASK-0050: Checked FFI, Regions, and Scoped Control Program](TASK-0050-checked-ffi-regions-control-program.md)
  coordinates the staged program. Its [plan](plans/checked-ffi-regions-control.md)
  retains the complete acceptance map and checkpoint ownership. M1 has an accepted
  semantic contract; product and Linux realization gates remain pending.

The generic cell product checkpoint is integrated into local `main`. Its
[case map, verification and local history](../design/generic-cell/evidence.md)
record the completed transition, Main integration and exact scope.
[DN-0054](../design/DN-0054-base-lexical-region-memory-contracts.md)
remains separate design work.

## ffi-ash closure coordination

TASK-0041 is superseded for closure coordination by the existing
[issue #7 handoff](https://github.com/dikini/ash-lang/issues/7#issuecomment-6234064548).
The [exact task history](https://github.com/dikini/ash-lang/blob/7471200efb1bd90782fcad81be54b992fbd92982/docs/tasks/TASK-0041-ffi-ash-milestone-closure.md)
preserves its work and findings. The handoff carries all final Main verification,
acceptance and checkpoint-lifecycle obligations; supersession does not complete
or waive them. The
[TASK-0042 performance record](../project/verification-performance-2026-10-20.md)
retains the completed controlled comparison and tooling findings. The completed
task and its owned execution plan are retired; Git retains their history.
