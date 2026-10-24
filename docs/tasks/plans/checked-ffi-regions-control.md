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

Root assigns each stage. The user has authorized removal of unnecessary code;
PR138 delivered the first retirement. S1 independently reviewed CP-0024's
accepted mapping; S2 implementation follows design retention and assignment.
Existing machinery governs values and artifacts originating in FFI. Foreign
origin adds no admission, lifecycle or validation protocol.

Use this concrete sequence:

1. Delivered in PR138: the milestone-only artifact/receipt/protected-launch
   package, producer, root, leaf, link observers, APIs and dedicated tests were
   removed. Typed bridges, generic image/Core fixes, fingerprint/gas, managed
   Bytes, effects, handlers and cleanup remain. No Main reset.
2. S1 accepted CP-0024's opaque nominal Address, null/equality, synchronous
   read-only Bytes pointer arguments and ordinary symbol effects; no new memory API.
   Then replace inherited foreign policy in the existing entry and delete its obsolete dependency closure.
   Current shared checked source-projection/reconstruction and injected leaf
   policy tests remain only until this replacement; they are not a permanent
   compatibility stack. No new general resource-State mechanism is assumed.
3. Use ordinary Ash binding code and existing cleanup for the small normal/error
   example: make/fail/echo/release with ordinary null/error handling. Keep managed
   Bytes echo separate and never free its backing. Exercise SQLite libversion/
   sourceid pointer returns; report missing text readback and open/prepare C int/
   out-pointer shapes.
   Report actual gaps; do not add a shim to claim numeric representation support.
4. The developer owns focused ordinary build/image/nonforeign regressions and a
   workspace check for this removal. At the integrated slim path plus example,
   the developer runs the full normal gate before M1 acceptance/Main integration.
   This cleanup alone is not milestone completion.

Observed first-retirement editing/check time was about one active agent hour
before review, including fresh unit-test compilation. Estimated remaining active
agent elapsed time with one writer and parallel review: S1 0.5–1 hour;
S2 2–4 hours including mandatory obsolete source-policy retirement;
S3 0.75–1.5 hours; S4 0.75–1.5 hours, about 4–8 hours total.
Allow up to roughly 12 hours only if S1 exposes a concrete missing ordinary
memory/backing capability or policy deletion reveals generic Core/image coupling
that needs repair. These are estimates, not promises or a new mechanism budget.

The [old F1-F8 plan](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/tasks/plans/checked-ffi-regions-control.md)
is superseded as an active assignment. Its source/static results remain
historical evidence; unfinished security, host/quarantine, receipt/protected
launch, isolation and full SQLite obligations are deprecated or deferred, not
completed. No old evidence proves the new delivery. Root owns live issue status
and the stage-to-issue map.
