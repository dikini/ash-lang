# Smaller foreign-library boundary plan

Owned by [TASK-0050](../TASK-0050-checked-ffi-regions-control-program.md).
[CP-0024](../../proposals/CP-0024-checked-foreign-host-profile.md) records the
agreed responsibility boundary and proposed technical transition. This plan has
no independent semantic authority.

Overall [program #51](https://github.com/dikini/ash-lang/issues/51) still tracks
later [M2 #53](https://github.com/dikini/ash-lang/issues/53),
[M3 #54](https://github.com/dikini/ash-lang/issues/54) and
[M4 #55](https://github.com/dikini/ash-lang/issues/55). Their regions, retained
control and worker scope remains unchanged and later; it is not required for the
initial M1 FFI delivery. Each later milestone owns its scoped design gates.

| Stage | Planned work and completion condition |
| --- | --- |
| [S1 #131](https://github.com/dikini/ash-lang/issues/131) | Review bytes/raw-C-address representation, memory/lifetime interpretation, ordinary effects, and minimum reuse/removal. Select the actual API before implementation; begin with existing cleanup, handlers and memory/value abstractions. |
| [S2 #132](https://github.com/dikini/ash-lang/issues/132) | Implement only the reviewed supported representations and generated ABI calls in the existing path. Ordinary Ash modules own checks/conversions. Do not add numeric types, implicit conversions or a parallel policy stack. |
| [S3 #133](https://github.com/dikini/ash-lang/issues/133) | One small native example with ordinary Ash normal/error handling and existing cleanup/handlers. Foreign/local resources follow the same abstract rules; no new State/copy subsystem is a prerequisite. |
| [S4 #134](https://github.com/dikini/ash-lang/issues/134) | Integrate the connected product, specification/docs and focused regressions; run the normal workspace gate and independently review delivery. |

[Parent #52](https://github.com/dikini/ash-lang/issues/52) owns the revised delivery. [SQLite canary #133](https://github.com/dikini/ash-lang/issues/133) is required
during S1 design and S3/S4 integration. After S1 design, exercise representable
calls and report
concrete unsupported cases, differences and gaps. Keep contracts/checks in
ordinary Ash. The small fixture complements rather than replaces the canary.
Full SQLite coverage is not required now. Discover C-aligned primitive needs as
they arise and report them for later prioritization; no fixed type catalogue,
scheduled extension phase or numeric-delivery prerequisite follows.

Root assigns each stage. This checkpoint revises planning and issues only;
implementation, native runs and product cleanup remain held. Detailed pointer
API/memory mapping is S1 work, not a decision inherited from earlier drafts.

The [old F1-F8 plan](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/tasks/plans/checked-ffi-regions-control.md)
is superseded as an active assignment. Its source/static results remain
historical evidence; unfinished security, host/quarantine, receipt/protected
launch, isolation and full SQLite obligations are deprecated or deferred, not
completed. No old evidence proves the new delivery. Root owns live issue status
and the stage-to-issue map.
