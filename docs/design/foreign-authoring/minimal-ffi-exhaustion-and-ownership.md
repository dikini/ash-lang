# Exhaustion-safe FFI reporting and ownership preservation

This design refinement belongs to
[DN-0057](../DN-0057-checked-ffi-module-boundaries.md) and the
[copied-text and connection/statement cases](minimal-ffi-contract-cases.md).
It resolves their remaining reporting/ownership policy at design level,
subject to review, semantic adoption and implementation evidence. It selects
no source syntax and authorizes no implementation.

## Common contract and existing limits

These rules are platform-independent. They require an executor to support
admission, bounded control records, unique owner tracking and disposition
reporting. Isolated execution additionally requires session invalidation,
termination requests and observation of actual process termination. Exact
platform mechanisms belong to a deployment profile; this document requires
no particular executable format, syscall, allocator or process-control API.

Current Ash's [native-buffer execution](https://github.com/dikini/ash-lang/blob/2766e8260e2590d9ebdca7abd699115b3cd02a8a/spec/dynamic-semantics.md#scoped-native-buffer-execution)
prepares storage and release work before native allocation, keeps internal
exhaustion terminal, and gives no unconditional teardown guarantee. Its
[typed failure reporting](../../../spec/dynamic-semantics.md#typed-failure-reporting)
keeps body outcomes separate from completion errors. These are constraints
to preserve, not evidence that general FFI already exists.
The experimental [runtime](https://github.com/dikini/ash-lang/blob/2766e8260e2590d9ebdca7abd699115b3cd02a8a/src/foreign/runtime.rs) and
[evaluator](https://github.com/dikini/ash-lang/blob/2766e8260e2590d9ebdca7abd699115b3cd02a8a/src/eval/foreign.rs) additionally distinguish consumed and
retained owners from fallible error conversion. Transfer that distinction
without adopting the whole experimental adapter architecture.

## Failure classes

The [canonical precedence](minimal-ffi-transitions.md#common-outcome-precedence)
and [domain table](minimal-ffi-transitions.md#common-exhaustion-domains) own
classification. Evaluator/parent mandatory capacity failure is terminal to
that evaluation. Isolated worker-runtime exhaustion is session failure to a
healthy parent; a worker report cannot establish parent exhaustion. Returned
native NOMEM remains a native outcome, not evidence about either runtime.

A declared limit is an ordinary outcome only when its small result envelope
has already been admitted. Optional diagnostics have a separate bounded
allowance and may be skipped before allocation. Actual evaluator allocation
failure stays terminal. No global budget refill or retry follows refusal.

## Pre-admission and reserved records

Before native acquisition or an effectful call, reserve the control storage
and fixed host work needed for all of that call's admitted outcomes:

- Exact contract/operation, actual owner references, call phase and native
  status slots; no formatted strings or dynamically copied provenance.
- Acquisition guard, fresh activation and dependency edges before acquiring
  a connection or statement, including partial-acquisition outcomes.
- Scope/access publication storage and its bounded success/failure envelope.
- Separate local-completion K and native-disposition records, ordered report
  slots, quarantine capacity,
  and dependency-ordered host-teardown bookkeeping for each admitted owner.
- For isolation, pending-request/session record, bounded outcome-frame storage,
  validation work, invalidation flag and supervisor shutdown/reaping records.

Reservations precede native entry/dispatch, after operand evaluation as needed.
Earlier operand effects are not rolled back on refusal. Reservations cannot
be consumed by ordinary computation or optional diagnostic construction.
Bound identity counters and refuse before entry rather than wrap or reuse IDs.

Payload sizes not yet known, such as a column length, require a second check
before allocating/copying that payload. The already reserved control record
can retain the outcome of failing that check without allocating again.
Pre-admitting a control record does not reserve an arbitrary result graph.

Each owner reserves its own eventual disposition slot, not an unbounded event
history. Retain ordered completion records until the enclosing report has
been delivered or the runtime failure path has retained them. Charge retained
history against explicit capacity; sequential acquisitions do not bypass that
limit by releasing live-owner slots. Refuse new acquisition before native
entry when the required report capacity is unavailable. Emergency records
must not silently discard ownership facts or claim a truncated list complete.

Fixed control/report capacity is a bounded host guarantee under an intact
runtime. It does not reserve SQLite's internal allocations, make arbitrary
source cleanup executable after exhaustion, or ensure native termination.

## Ownership changes precede reporting

Track whether the call was not entered, entered but unresolved, or returned
with a recorded outcome. Store native status, protocol transition and known
consumption/retention in reserved slots immediately after a conforming return,
before diagnostic queries, encoding, allocation or source-result construction.
This host bookkeeping step must not allocate or charge unreserved work.

Only the unique owner record establishes consumption. Access aliases, ordinary
error constructors and optional diagnostics cannot change it. Once consumed,
clear the native access and remove its dependency edge exactly once; later
failure must not resurrect the owner or cause another native finish. Retained
or uncertain ownership cannot authorize source reuse or backing release.

Acquisition installs an unpublished guard immediately when the native contract
establishes an owner. Publish access only after its dependency/activation and
source-result admission succeed. If publication fails, the guard survives
and follows its admitted disposal/quarantine path. A contradictory native
address is not a conformingly acquired owner; follow the ABI profile's
quarantine rule instead of calling a destructor through suspect output.

## Minimal reporting and source outcomes

Keep a fixed runtime failure record separate from ordinary Ash values. It
contains cause/phase, operation and owner references, known native status,
disposition, diagnostic-availability reason and report-completeness state.
Use bounded IDs and references into already retained metadata. Creating this
record requires no heap allocation, native diagnostic query or source callback.
Rendering, localization and external output are later fallible operations;
failure to render cannot change the retained ownership facts.

For normal source completion, preserve the body result separately from ordered
completion reports. K1–K9 in the canonical table govern exact-once local
discharge. Session loss or quarantine permits local closure with a failure
record, never a stale native finish. A consumed or retained finish outcome is
recorded and discharges K before optional diagnostics; report failure cannot
recreate either authority. Reserve the envelope and report links before the
relevant ownership transitions. Materializing richer ordinary data may still fail;
that is terminal runtime failure, not a fabricated successful source return.
The runtime record can retain a reference to an already obtained body result
without promising to serialize or deliver it after exhaustion.

Primary runtime failure is not replaced by a later diagnostic or teardown
failure. Preserve separately the native status already observed, each known
owner disposition and subsequent completion/teardown failures. Missing detail
is marked unavailable, never translated to successful release. This record
is runtime evidence, not a first-class proof or source recovery mechanism.

## Copied text in-process

Admit fixed control/error delivery before entering the copy sequence. After
kind, pointer and matching length checks, reserve copy/UTF-8 work and payload
storage before reading the native interval. A configured length refusal is an
ordinary boundary outcome; exhausted runtime work/storage is terminal.

If admission fails, publish no string and close temporary access. The statement
remains in its known row state if native behavior conformed; terminal failure
does not continue the source body merely because that state is known.
If native text conversion reports NOMEM, retain that native status distinctly
from a later Ash allocation failure. Preserve the ABI profile's immediate
error-probe ordering; do not attempt optional diagnostics first.

Copy into unpublished storage and expose only the bytes actually written.
UTF-8 rejection publishes no string. Successful publication transfers the
independent value; later reporting or resource failure cannot invalidate it.
An incomplete copy never becomes an empty successful string. Release scratch
without granting an escaping native view or retrying the operation.

## Connection and statement in-process

Use L1–L22 of the [canonical lifecycle table](minimal-ffi-transitions.md#sqlite-acquisition-and-lifecycle-table)
for partial acquisition, unpublished-owner disposal and consumption/retention.
O4 records disposition before fallible reporting; O8 preserves it on evaluator
exhaustion. No second error-to-ownership mapping is defined here.

Consumed statement access cannot reappear even when source error construction
fails. Known retained dependencies block enclosing destruction before native
entry. Partial-owner disposal may itself fail or fail to return; neither
reserved bookkeeping nor a destructor invocation proves release succeeded.

## Isolated control and payload delivery

Reserve parent pending-operation and acquisition/proxy capacity before sending
any request bytes. The worker must reserve its guard/control capacity before
native entry, but the parent never trusts it to have done so. Give every
operation a fixed-size, independently bounded outcome frame, followed only by
its declared bounded value payload and optional diagnostic payload. The
outcome frame contains expected session/request/operation/resource identities,
native outcome/status and permitted ownership/protocol disposition. Frames
have no arbitrary embedded allocation size, pointer or source authority.

Validate the complete outcome frame and expected transition with pre-admitted
parent work/storage. A partial header, unvalidated frame or out-of-order reply
establishes no completion. Once a complete frame is admitted, commit the
known disposition before allocating or decoding later payloads. It is still
a foreign report under the stated assumptions, not proof of worker behavior.

Apply O1–O10 and X1–X5 from the canonical tables: preserve admitted control
before later payload failure; distinguish worker exhaustion from parent
exhaustion; never infer successful source delivery from control alone.
Optional diagnostic draining is bounded and pre-admitted, or the session ends.

An admitted native outcome without a required payload is not successful source
delivery. Parent runtime exhaustion terminates evaluation; its already
admitted supervisor path can invalidate/stop the worker without allocating a
fresh request or relying on its cooperation. Oversized/malformed frames lose
the session rather than cause unbounded buffering or draining. A worker that
cannot send its reserved outcome may die; the parent still follows the
unknown-completion path. No acknowledgement is presumed to arrive under OOM.

## Terminal disposal and executor obligations

On evaluator exhaustion X1, stop ordinary source evaluation and transfer
unfinished K through K8 without claiming source cleanup. Do not invoke arbitrary
source cleanup, replay completion, increase limits or promise source recovery.
Worker exhaustion X4 instead loses that session: a healthy parent can handle
the boundary failure and discharge its local scopes through K4 in order.
Transfer live guards to already reserved host disposal records on terminal
source evaluation, separately from local discharge in a healthy parent.
Use retained dependency order; never discard backing while a dependent may
still need it. Record whether native completion was unattempted, returned or
unresolved so host teardown cannot replay an operation already known consumed.

In-process teardown may invoke only the separately admitted native disposal
path, not source code. It needs an explicit contract for each still-live owner.
If a finish already refused, do not silently retry it as guard destruction.
Retain/quarantine the owner and required backing when safe release cannot be
established. This may retain native storage until host termination; capacity
remains charged. There is no eventual-release or native-call time bound in
this mode. External termination can prevent all subsequent reporting.

In isolation, the supervisor requests termination using reserved platform
control resources, observes actual termination and reaps before retiring the
session's reservations. Until then, keep the session inaccessible, its grant
reserved and its termination state explicit. Native completion not already
acknowledged stays unknown; process reclamation is a different fact. Preserve
persistent data/journals. Platform mechanisms and their limits belong to the
[launch profile](minimal-ffi-launch-and-artifacts.md), not this common contract.

## Closure evidence

Fault-inject each fallible reservation before entry and each conversion after
return, separately from native NOMEM. Cover exact budget, one-short budget and
a fresh sufficient run without retrying effects from the failed execution.
Verify no partial value/owner publication and no loss of primary failure.

For copied text, distinguish native conversion failure, configured size refusal,
runtime allocation refusal, invalid UTF-8 and isolated payload loss. For
ownership, inject failure after open returns a partial owner, after prepare
returns a statement, after finalize consumption and after close retention.
Observe exact-once consumption, preserved dependencies, unavailable diagnostics
and no source continuation after terminal exhaustion.

For isolation, fail before dispatch, during a partial outcome frame, after a
complete consumed frame and during subsequent payload/diagnostic delivery.
Exhaust normal evaluation while a request is pending and verify the supervisor
does not need new allocation to invalidate and request termination. Test delayed
reaping and refusal of further admission while reservations remain charged.
Reserve-capacity accounting must include retained report history and quarantine.

Together with the canonical transitions, SQLite policy, checked representation
and explicit target/executor profiles, this supplies proposed design rules for
the four identified blockers. The canonical tables own their combined meaning.
It is not implementation or production-readiness evidence. Semantic adoption,
architecture decisions and authorized delivery with positive/negative checks
remain necessary. Syntax, exact runtime structs, wire encoding and platform
API implementations remain unselected.
