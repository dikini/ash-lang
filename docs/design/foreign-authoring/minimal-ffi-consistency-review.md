# Minimal FFI contract consistency review

This review belongs to [DN-0057](../DN-0057-checked-ffi-module-boundaries.md).
It concerns the copied-text and connection/statement cases before source
syntax. Earlier and revised-table findings now have proposed canonical
resolutions. This record is not implementation verification or independent
acceptance evidence.

## Assessment

The [canonical transition tables](minimal-ffi-transitions.md) now own combined
outcome, exhaustion-domain and lifecycle behavior. Supporting documents refer
to those rules. Common FFI guarantees, SQLite library policy and target/executor
profiles have separate owners. Linux profile acceptance remains open.

The canonical tables now distinguish entry admission, pending observations,
result delivery, failure events, local completion and physical reclamation.
R1–R3 have explicit proposed rules below. Linux-specific acceptance is unchanged
and remains a separate gate; no syntax or implementation is selected here.

The final consistency pass confirms the earlier phase, outcome, exhaustion,
encoding and ownership distinctions. F1's local-close precedence was approved
and is now recorded in the canonical table, with exclusive fallback guards
and distinguishing traces. No common-contract finding remains open in this
review's two-case scope. Implementation evidence and Linux acceptance remain
separate; this is not an approval of current language semantics or architecture.

## Common and library findings addressed at design level

| Finding | Resolution and owner |
| --- | --- |
| C1: Transport loss could erase an admitted disposition. | O1–O10 preserve admitted control independently of payload delivery and session loss. |
| C2: Worker exhaustion could be mistaken for parent exhaustion. | X1–X5 name the evaluator, native, operation-limit, worker and supervisor domains. Worker reports cannot establish parent exhaustion. |
| C3: Portable SQLite semantics were mixed into the Linux ABI profile. | [SQLite policy](minimal-ffi-sqlite-policy.md) owns C signatures, constant roles, inputs and assumptions; [ABI profile](minimal-ffi-abi-profile.md) owns concrete target mapping; common transitions are separate. |
| S1: Reset could erase binding uncertainty or other access restrictions. | L1–L23 keep execution, bindings, access, disposition and session coordinates separate, with conjunctive preconditions. Physical quarantine retains executor backing beyond source scope closure. |
| S2: Original kind was not retained across repeated column reads. | T1–T16 use a bounded lazy classification cache keyed by row generation and column, established before conversion and invalidated on native row-changing entry or access loss. |

SQLite's original-kind restrictions derive from
[column access](https://www.sqlite.org/c3ref/column_blob.html). Reset and
binding behavior derive from [reset](https://www.sqlite.org/c3ref/reset.html)
and [binding values](https://www.sqlite.org/c3ref/bind_blob.html); the wrapper's
uncertainty policy is deliberately conservative. Canonical rows and their
acceptance traces are proposed Ash binding behavior, not additional promises
made by SQLite.

The trace table covers bind-error/reset/step, finalize-error/diagnostic-loss,
worker exhaustion with a healthy parent, repeated copies after refusal, close
refusal followed by source-host closure, failed acquisition publication and
reset error after a row. These are stated obligations, not executed results.

## Revised-table findings addressed at design level

| Finding | Canonical resolution |
| --- | --- |
| R1: Entry guards excluded failure events and mixed phases. | The phase/guard table and O/L phase columns separate Admission, Entry, Observation, Delivery, Failure, Local close and Reclamation. Pending-return validation uses the saved admission state; processing loss requires no live executor or usable source access. |
| R2: Local completion after loss/quarantine was absent. | K1–K9 distinguish source completion from native disposition. Pending scopes close at their structural positions; Closing scopes settle locally on loss; admitted finish discharges K before reporting. K7 prevents a second attempt/report; K8 transfers on terminal evaluator failure without claiming source cleanup. |
| R3: Invalid native bytes and malformed worker success were conflated. | T10 is native conversion refusal, T14 admits a valid worker refusal, T15 loses the session on invalid success payload, and T13 keeps parent capacity exhaustion terminal. T16 alone publishes an admitted parent success. |

See [phase guards](minimal-ffi-transitions.md#phases-and-event-guards),
[local completion](minimal-ffi-transitions.md#common-exact-once-local-completion)
and [copied-text transitions](minimal-ffi-transitions.md#sqlite-copied-text-table).

The group processes events in one order. Failure selection prevents a late
success response, while previously admitted native disposition remains intact.
Late frames cannot reopen a lost session. An unpublished guard or worker-native
guard has executor disposal authority, not another source K obligation.
Physical reclamation does not itself discharge a Pending source owner or
claim native completion.

Required traces include worker death before control, close blocked before
entry, handled loss followed by S/C scope exit, finalize acknowledgement before
diagnostic loss, and conversion refusal versus malformed success versus parent
validation exhaustion. Existing capture/resume/discard constraints still apply;
local bookkeeping discharge does not permit skipping an executing source action.
These are acceptance obligations, not executed verification evidence.

## Final review finding resolved

### F1: Order overlapping local-close reasons

The approved selection rule is recorded in the
[local completion table](minimal-ffi-transitions.md#common-exact-once-local-completion):
already discharged/transferred owners stay unchanged; terminal evaluator
failure transfers unfinished obligations; healthy Pending scopes wait for
their closing position; healthy Closing scopes select session loss, then
quarantine/contract violation, then blocked dependency, before native entry.

K4–K6 have corresponding fallback guards. One primary completion record retains
other conditions as secondary facts without another report or native call.
Atomic O4/K3 still protects an already admitted finish. The trace table covers
loss plus dependency, quarantine plus unresolved child, terminal failure plus
loss, and already discharged consumption followed by failure.

F1 is resolved at approved design level. The traces remain implementation
acceptance obligations, not executed verification results.

## Linux profile acceptance gaps

The [launch sequence](minimal-ffi-launch-and-artifacts.md#trusted-launch-sequence)
specifies namespace mappings and dropping capabilities before exec, but does
not fix the post-exec UID/capability state. No host-root mapping is not the
same as non-root credentials inside the namespace. Linux recalculates
capabilities on exec; see
[user namespaces](https://man7.org/linux/man-pages/man7/user_namespaces.7.html).
Require verified post-exec credentials/capability invariants, including
re-execution of the admitted image, with an explicit launcher configuration.

The exact syscall allowlist, root/volume construction and resource enforcement
need a tested deployment realization. Startup, SQLite journal/locking and
forced termination must work under those restrictions. A second platform is
not a prerequisite for common syntax design, but the Linux realization cannot
be called accepted or production-ready from its policy description alone.

## Remaining acceptance boundary

The earlier findings and R1–R3 have explicit proposed design resolutions.
F1 now has its approved canonical selection rule. No common finding remains
open within this review's two-case scope. This record
does not substitute for independent acceptance or implementation evidence. Linux
credential/syscall/deployment acceptance remains separate. Check
source/module/Core/runtime correspondence and negative cases during semantic
adoption. Exact runtime structs, versioned wire/receipt encoding and platform
API implementations remain constrained implementation choices. General
borrowing, callbacks, asynchronous native APIs, more platform profiles and
formal proof machinery remain outside these two cases.
