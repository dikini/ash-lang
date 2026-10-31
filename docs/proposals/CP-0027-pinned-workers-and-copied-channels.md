# CP-0027: Pinned workers and copied channels

- ID: `CP-0027`
- Status: accepted
- Related: [AD-0017](../decisions/AD-0017-pinned-worker-host-and-transport.md), [DN-0055](../design/DN-0055-algebra-of-regions-lifetimes-and-ownership.md), [DN-0056](../design/DN-0056-scoped-continuation-retention-and-library-scheduling.md), [DN-0058](../design/DN-0058-pinned-worker-host-and-channel.md), [TASK-0058](../tasks/TASK-0058-pinned-worker-network.md)

> This accepted transition authorizes bounded product work; it is not current
> Ash. The independent contract review covered head
> `b296e17ce9e4f1760ce73df4f4716ef0c0fb2093`. Required product, proof and
> integration evidence remains pending. On 2026-10-31 the user superseded
> protocol-specific compiler checking and later ruled out new runtime checking
> machinery beyond ordinary error handling. The endpoint and settlement
> refinement below is proposed under that direction, not implemented truth.

## Current behavior

The [retained-control rules](../../spec/static-semantics.md#scoped-retained-control)
give a Store its own slots and require actual branch and cleanup completion;
its [execution](../../spec/dynamic-semantics.md#scoped-retained-control-execution)
moves control into and out of that Store. A key names a generation and carries
no ownership. [Regions and cells](../../spec/static-semantics.md#lexical-regions-and-construction-dependencies)
retain actual storage and resource dependencies. Current Ash supplies neither
the worker admission nor the channel and network completion contract below.
The [foreign boundary](../../spec/static-semantics.md#source-foreign-declarations)
does not prove native behavior or create process isolation.

## Proposed behavior

### Workers and entry

One network activation owns exactly two worker executions and their channel
support. Each worker runs its Ash execution and local Store on one carrier
thread for its lifetime; pinning here is thread affinity, not CPU affinity.
The kernel may preempt that thread without any Ash capture, restoration,
transfer, cleanup, or completion. Only the owning worker drives its Store;
a peer notification is a request to its owner, not authority to restore it.

The initial entry form must resolve to a known top-level function with no
captured environment. Its explicit startup inputs are copied bytes and the
designated endpoint capabilities established by the network activation. The
admission check traverses selected code and evidence dependencies: it rejects
any retained caller-local region, cell, Store, handler, provider, native pointer,
closure environment or cleanup authority. Unresolved or foreign dependencies
whose admissibility cannot be established reject. Worker-local resources,
providers and retained control are acquired after entry on that worker. This
closed entry rule is intentionally narrower than general closure transport.
The eventual source and Core representation must make this admission and its
identity reconstruction explicit; an ordinary same-typed callback is not proof.
Admission authenticates the actual resolved definition, linked body and selected
evidence, rather than its spelling. The host injects each designated capability
only into its assigned worker entry after network preparation; source data and
copied bytes cannot construct it. The entry can invoke ordinary imported helpers
and build library executors after entry, provided their actual transitive
dependencies satisfy the same admission rule. No live heap, Store key, selected
handler or captured caller control crosses the entry boundary.

Before entry commits, failed preparation leaves caller-owned resources and
inputs with the caller and publishes no worker authority. After entry commits,
the worker owns its local execution and completion obligations. A later failure
does not move them to the caller or promise recovery. An enclosing network owner
retains backing and the obligation to coordinate settlement. Partial construction
and failure may report incomplete teardown; already performed effects remain.

### Entry and endpoint representation

This transition specifies a representation; it does not define current Ash.
The defining identities below belong to a new sealed
`@builtin.network` module. An import alias is ordinary. The proposed acquisition
has this shape:

```text
resource Network.Pair<N> pair = (capacity, start_a, start_b, input_a, input_b) {
    coordinator_body
}
```

N is fresh. Capacity is a positive finite integer and the startup inputs are
`Bytes`. Each start operand names a resolved, top-level function, polymorphic
in N, with entry shape `(Network.Worker<N>, Bytes) -> Unit ! rho`; the compiler
instantiates the actual linked function once for the worker. These operands
are function designators rather than evaluated closure values. A local or
computed callback is inadmissible. Check actual linked bodies, selected evidence
and transitive dependencies, including imported helpers, under the admission
rules above; an empty outward row does not prove this check. Surrounding source
handlers are not inherited. After N instantiation, the entry row must be closed
and contain only the canonical default allocation instance, `Network.IO<N>`,
and admitted native symbol instances. Worker entry discharges default allocation
with its own host-backed root, `Network.IO<N>` with its injected interpreter,
and native instances with the existing native-binding admission mechanism.
No other host service, open row, constrained entry scheme or inherited handler
is admitted. An entry may install ordinary source handlers and local providers
internally. Each native binding must be valid on that worker, and its ordinary
foreign contract is an assumption: this check does not prove thread safety,
native memory correctness or containment. A native call is synchronous and
occupies the carrier until return; it does not transport its stack.
The same native binding may refer to shared Rust or C state even when Ash roots
are separate. Its binding/module contract must permit every overlapping worker
invocation and any later native use; thread safety, pointer lifetime and
foreign state settlement are assumptions on that ordinary contract, not facts
derived from Ash isolation or a checked FFI protocol.
Each worker creates a fresh local root heap and reconstructs its global callable
and evidence environment from the admitted linked definitions. Immutable code
metadata may be shared only when its actual representation is safe for
concurrent access; runtime closure records, global values, selected handlers and
caller-root allocations are not shared. Initialization and its failures run on
that worker after commit, and initialized local resources are owned there.
Admission includes every reconstructed global initializer, its selected
evidence and native symbols, and checks its effects against the same closed row
and local-interpreter conditions. Each worker uses its own initialized values; no
initializer is replayed across failure to simulate rollback.

Capacity and input operands evaluate once, left to right, in the preceding
scope. Preparation copies both inputs with their source owners live, allocates
support and prepares both carrier entries. Neither may execute Ash before the
single network entry commit. Commit requires both injected `Worker<N>`
capabilities and prepared carriers; only afterward does the coordinator body
run. Failure before commit joins or otherwise settles prepared carriers and
publishes neither capability nor activation. Incomplete teardown is reported
and leaves affected backing protected. Failure after commit follows worker
ownership rather than moving its control to the coordinator. N and all handles
and retained dependencies naming the activation cannot escape the owner.
Capacity must fit the host queue representation; an unsupported size or storage
refusal fails preparation without publishing an activation. Capacity bounds
the number of accepted undelivered messages, not their byte size.

Each injected `Worker<N>` contains authenticated activation and side identities.
Side A sends on A-to-B and receives on B-to-A; side B has the opposite
polarities. Source bytes, integers, matching types and user implementations
cannot forge these identities. `Pair<N>` grants coordination rather than
worker-local Store or endpoint authority. Worker handles may have local aliases;
the actual endpoint interpreter serializes each polarity, and reentrant or
overlapping operations cannot start a second operation. Endpoint completion
belongs to the activation, not to an alias.

The first host implementation uses these sealed, nonblocking operations:

| Operation | Proposed result and state change |
| --- | --- |
| `try_send(worker, bytes)` | `Sent`, `Full`, `Closed` or terminal failure. `Sent` atomically accepts and publishes a complete copied snapshot. `Full` and `Closed` commit nothing. |
| `try_receive(worker)` | `Message(kind, bytes)`, `Empty`, `End` or terminal failure. `Message` commits only after a complete receiver-region copy; a failed copy leaves the entry. |
| `send_control(worker, bytes)` | Sends a control envelope using the same queue, commit and failure rules as `try_send`; its actual sealed operation establishes the sending side and Control kind. |
| `finish_send(worker)` | Irreversibly seals this send polarity after earlier operations resolve. |
| `finish_receive(worker)` | Completes the receive polarity after actual transport End and applicable transport operations resolve; it does not attest that each message was processed or cleaned up. |
| `settle(pair)` | Returns normally only after worker scopes and endpoints complete, backing users settle and no later callback is possible. |
| `watch(worker, interest)` | Registers readiness interest for this side and activation, rechecks the predicate, and returns an opaque local registration. |
| `cancel_watch(worker, registration)` | Cancels that registration and settles possible notifications before its support can be released. |
| `poll_wake(worker)` | Returns a pending local registration identity, or no wake. Duplicate and stale identities do not authorize restoration. |

The defining module exposes ordinary nominal result sums with these cases:
`SendResult = Sent | Full | Closed | SendFailed(Failure)`,
`ReceiveResult = Message(EnvelopeKind, Bytes) | Empty | End | ReceiveFailed(Failure)`,
`WatchResult<N> = Watching(Registration<N>) | WatchFailed(Failure)`, and
`WakeResult<N> = Wake(Registration<N>) | NoWake | WakeFailed(Failure)`.
`EnvelopeKind = Application | Control` identifies the actual received envelope
class; the peer is the opposite side of the fixed channel.
`Failure = Refused | Uncertain | WorkerFailed | IncompleteTeardown` identifies
definite pre-commit refusal, unknown send acceptance, terminal worker failure,
and incomplete teardown respectively. Finish, cancel and settle return either
`Ok` or `Failed(Failure)`. These are reporting values, not proof tokens; no case
means a failed operation's cleanup completed. The host transitions to terminal
failure when it cannot safely continue; it cannot resume ordinary network work
merely because a source handler constructs an `Ok` value. An uncertain send
retains its reservation until authenticated resolution, as specified below.

`try_send`, `try_receive`, `watch`, `cancel_watch`, `poll_wake` and endpoint completion use
an identity-indexed sealed `Network.IO<N>` effect interpreted by the injected
worker activation. The coordinator's `settle` uses a separate sealed
`Network.Join<N>` effect interpreted by the owner. Neither effect gives a
source handler the ability to mint endpoint or completion facts.
The exact monomorphic types after instantiating N, with `delta` denoting the
canonical private default allocation instance, are:

```text
try_send       : (Worker<N>, Bytes) -> SendResult ! {IO<N>, delta}
send_control   : (Worker<N>, Bytes) -> SendResult ! {IO<N>, delta}
try_receive    : Worker<N> -> ReceiveResult ! {IO<N>, delta}
finish_send    : Worker<N> -> FinishResult ! {IO<N>, delta}
finish_receive : Worker<N> -> FinishResult ! {IO<N>, delta}
watch          : (Worker<N>, Interest) -> WatchResult<N> ! {IO<N>, delta}
cancel_watch   : (Worker<N>, Registration<N>) -> FinishResult ! {IO<N>, delta}
poll_wake      : Worker<N> -> WakeResult<N> ! {IO<N>, delta}
settle         : Pair<N> -> FinishResult ! {Join<N>, delta}
```

`Interest = Readable | Writable` and `FinishResult = Ok | Failed(Failure)`.
The allocation instance denotes the existing default allocation requirement,
not a new public effect name. Operand effects and result construction retain
the ordinary row-union rules. `Registration<N>` is an
opaque activation, side and generation locator, not ownership. Its generation
cannot wrap into an earlier registration; exhaustion fails before publishing it.
`cancel_watch` succeeds only after no new wake for that registration can be
issued; already queued stale wakes can be consumed but cannot restore control.
Cancellation and settlement must remain serviceable without blocking the peer's
executor indefinitely; neither promises scheduling progress.
The network owner supplies and discharges `Join<N>` within its scope; worker
entry supplies and discharges `IO<N>` within its execution. Neither instance
may escape through a result, outward row, captured evidence or cleanup.
Registration plus the readiness recheck is indivisible with respect to
predicate changes: an already-ready predicate produces a wake, while a later
transition to readiness produces one unless cancelled. Wakes may coalesce; a
consumer rechecks state rather than counting notifications.
`Readable` is ready when `try_receive` can return `Message`, genuine `End` or
`ReceiveFailed`; only `Empty` waits. `Writable` is ready when `try_send` can
attempt a send or return `Closed` or terminal `SendFailed`; only `Full` waits.
Readiness does not promise that subsequent snapshot allocation succeeds. A
seal or terminal failure makes the corresponding interest ready even when it
was registered afterward; no later state change is needed to wake it.
The recheck queues a pending wake for the returned generation before `watch`
returns if the predicate is already ready. `poll_wake` removes at most one
pending wake and readiness is level-triggered: if the registration remains
active and the predicate remains ready, another wake is pending or is queued
before the executor parks. Successful cancellation prevents new wake issuance;
previously queued wakes for the invalidated generation are harmless. Test the
publish-before-register, register-before-publish, poll-before-publish,
readiness-between-recheck-and-park, cancel-versus-publish, and late registration
after seal or terminal failure for both interests. A sealed empty channel wakes
Readable for End; a sealed sender wakes Writable for Closed.
An authenticated `End` or normal settlement result is related to the selected
interpreter, activation and current state; a user-created constructor, matching
type, intercepting handler or stale result supplies no such relationship. Empty
and Full allow a local executor to retain its own continuation and recheck
later. Private host wait registration uses the recheck and settlement rules in
[DN-0058](../design/DN-0058-pinned-worker-host-and-channel.md).
The wake identifies the registration, not a Store key; the local executor maps
its current registration to its own retained continuation and checks its
generation before restoration. A wake is a hint, and cancellation or
replacement invalidates an old wake. The executor keeps receive and control
service possible while application sends wait for bounded capacity, including
when an application continuation awaits a reply. The host cannot make progress
by restoring a worker's Store on another thread.

Atomic acceptance and publication makes the abstract accepted-unpublished
sequence empty in this implementation. The general contract still accounts for
that sequence if a later provider separates the commits. Private transport tags
and the actual sending channel establish envelope kind and peer; arbitrary
application bytes do not. A narrow sealed emission operation authenticates that
origin only. `try_send` always emits Application; `send_control` emits Control.
Both use one FIFO in each direction, so receive never skips an earlier envelope.
The actual interpreter associates the returned `Message` case with the tag and
peer of that delivery. Constructing the same result in source or intercepting
the request cannot establish that association. The sealed operation and side
establish transport origin; the host does not interpret control bytes or certify
an application's ledger, acknowledgement or completion. The earlier requirement
that a compiler follow the protocol driver's bodies, captures and imports to
confine raw publication and `send_control` is superseded. Applications must not
infer protocol correctness or honest completion merely from a Control tag.

#### One-way receive completion refinement

The earlier one-way refinement required linked analysis to attach a separate
processing obligation to each received Message, prove its local completion and
suffix, and allow `finish_receive` only after all such obligations were
cleared. That refinement, including its checked source fragment and per-message
completion guarantee, is superseded on 2026-10-31. `finish_receive` completes a
transport receive polarity only after the actual incoming channel is sealed,
empty and free of pending transport operations. It may occur while ordinary
application processing continues; it does not assert that any particular
message's application work or cleanup completed. Constructed End,
intercepted results, and an ordinary Boolean do not establish transport End or
settlement.

The proposed replacement relies on actual worker lifetime: a successful owner
settlement waits for both worker executions to return normally, their existing
generic Store and cleanup obligations, endpoints and backing users, and actual
carrier teardown and joins. Worker-local copies and their support remain owned
by the carrier through its return and owner teardown. Terminal failure follows
AD-0017's retention and incomplete-teardown contract; it does not claim normal
settlement. This is a narrower guarantee than the former per-message rule: a
program can return without carrying out its intended protocol. Work/Ack and
ordinary error handling are application behavior under CP-0028; the host does
not prove that behavior.

The retained N2 implementation has per-delivery tracking and a settlement gate
that must be reconciled with this revised worker-lifetime contract. Removing a
finish precondition alone does not establish correct delivery retention or
settlement. Review the actual receive, failure, worker return and owner teardown
paths together; keep generic C3 and native resource contracts. The earlier
one-way proof and checker evidence remains evidence of its original contract,
not of this revision.

Lower acquisition to an explicit Core network owner carrying the fresh identity,
resolved entry binders and instantiations, capacity and startup operands. Lower
operations to sealed, identity-indexed Core operations with the actual
activation and injected side, and explicit normal and terminal-failure paths.
Independent linked Core validation continues to enforce generic entry, type,
effect, resource and retained-control requirements and the authenticated network
boundary. It does not reconstruct the application protocol, confer per-message
completion facts, or enforce confinement of protocol producers. Generic
validation exhaustion cannot publish partial permission.

The Core owner records `(N, capacity, entry_a, entry_b, input_a, input_b, body)`.
Entry records carry resolved defining binders and their N instantiations,
dependency identities and effect rows; the worker capability is generated by
entry and cannot be supplied as a Core literal. A Core operation records its
defining operation identity, N, evaluated capability and ordered operands. Its
continuation distinguishes normal results and terminal failure. Validation
reconstructs the linked definitions and dependencies rather than trusting these
records as certificates. The bounded traversal covers transitive initialization,
calls and selected evidence and charges before traversal or retention;
exhaustion publishes no entry or close permission. The selected interpreter and
activation must match before an operation result establishes a fact; relevant
intervening state changes invalidate that fact.

At runtime send prepares the copy and insertion, then atomically commits
acceptance and publication and returns `Sent`. Receive prepares a receiver copy
before removing the FIFO head and returning its authenticated kind and bytes.
Finish-send seals after earlier accepted operations resolve. End requires sealed
and empty under the same synchronization. Watch installs a generation and
rechecks readiness atomically; wake only nominates that local registration.
Settlement requires actual worker, endpoint, wait and callback completion and
excludes future backing users before returning `Ok`. Terminal failure preserves
committed messages, owners and support; uncertainty allows neither retry nor
reservation retirement. These commit rules do not prove native or OS code.

This contract fixes the initial row, services and error cases. The exact syntactic
representation must preserve these defining identities and behavior. Bounded
proof and product verification remain required before release relies on them.

### Payload and endpoint authority

Each direction has one sender and one receiver, fixed for the activation. A
capability grants only its designated polarity and cannot be transferred to a
third worker, duplicated into another producer or consumer, forged from an
ordinary value, or reopened after completion. Local aliases must not duplicate
completion authority or enable concurrent endpoint operations. The network
owner protects channel backing but does not acquire either worker's local Store
authority.

The first transport payload is exactly a finite sequence of byte values, not a
recursive Ash object or a dependency-free type predicate. The entry and send
adapters must read the actual live byte contents while their source owner is
protected, allocate independent channel-owned storage and copy every byte before
acceptance. Receive allocates in the receiver's currently selected live region
and copies the complete sequence there before receipt commits. A source region
remains protected throughout the source read; it is never exported or moved.
Unbounded integers, arbitrary records, closures, and `Address` are not eligible
transport representations just because no resource dependency is visible.
Encoding them as bytes requires an ordinary library operation whose effects,
allocation and source dependencies obey current rules.
Neither a pointer, handle, endpoint, continuation, provider, cleanup obligation
nor a representation containing such authority is carried by those bytes.
Encoding application values and decoding them locally are ordinary library
work; a byte pattern does not authenticate a control fact. This restriction
avoids a general graph-copy rule, including cyclic graphs and sharing identity.
Typed codecs can represent request/reply data and finite-list ledger metadata
without fixing an application protocol in the transport. Both workers may run
ordinary retained computations that encode and decode local data; their live
continuations remain local. This representation fulfills the initial
resource-free copied-message goal, but does not promise transparent copying of
every resource-free Ash value. Integration evidence must demonstrate the actual
codec and cross-milestone example; inability to do so returns to this proposal.
Allocation or decoding failure is observable and cannot silently transfer an
owner or discard committed delivery obligations.

### FIFO, commits and waiting

Each direction has a positive finite capacity. Successful admission of a send
commits an accepted delivery obligation and a complete independent snapshot;
all fallible preparation precedes that commit. Before it, full, closed, or
failed preparation leaves the caller responsible for its operation and source.
After it, cancellation or failure cannot retract the message or pretend it was
never accepted. If an adapter cannot distinguish acceptance from a failure
reported by transport, its outcome is uncertain: it retains the reservation and
all affected support, does not retry or retire it as unaccepted, and reports
terminal failure unless an authenticated resolution establishes the outcome.
Accepted messages may await publication; that pending state is
protected and counts against the bounded capacity. Acceptance order determines
publication and receipt order. Publication commits the initialized entry into
the queue and makes its bytes visible to the receiver. Receipt commits only
when a receiver-owned copy is complete and responsibility for the delivery is
established; before that commit a failed copy leaves the queue entry intact.
Once receipt commits, its copy and support remain worker-local; application
processing and cleanup are not certified by transport receipt.

The abstract accounting is `accepted = received ++ queued ++ pending`, in
acceptance order, with `length(queued) + length(pending) <= capacity`. The
implementation may make acceptance and publication one atomic transition; it
must still preserve the pending-state obligation if it separates them. It must
not allow later publication or `End` to overtake an earlier accepted send.
Transport does not implicitly redeliver a committed receipt. Application
processing is the ordinary program's responsibility. A reported terminal
failure retains or disposes support only under the explicit failure contract;
it does not claim normal settlement.

A full send or empty receive may wait without losing the operation or its
owner. Registration and a subsequent readiness recheck must prevent a wakeup
from being lost between observation and parking. Wakes are hints: a duplicated,
late or stale notification must recheck current channel state and the local
Store generation; it cannot complete a different wait, restore a spent slot, or
confer authority. No Ash or native stack is moved to another worker. A blocking
host operation occupies its carrier; progress and fairness are not guaranteed.

### End and settlement

`finish_send` seals the send polarity only after all earlier accepted sends are
accounted for. It is irreversible and prevents future acceptance. A receive
returns authenticated `End` only when the polarity is sealed, no accepted
publication remains pending, and every earlier queued message has been
received. A temporarily empty queue or application bytes spelling `End` cannot
establish this fact. The receiver continues to service the bounded queue while
the sender finishes. Endpoint completion alone is not worker return or cleanup.

Backing may be released only after both workers actually return, both endpoint
completions and all pending
operations, wait registrations, callbacks, notifications and other backing
users have actually settled, and no future callback or wake can be issued
against that activation. A worker's local quiescence, receipt of `End`, or
an application-quiescence observation alone is insufficient. Normal and
abandoned exits require separate checked completion paths; an unprovable close
is rejected. Terminal failure may leave support unreleased and cannot turn an
unproved close into a release permission.

## Semantic delta

The proposal adds admitted worker entry, dedicated copied transport, and
authenticated transport and endpoint behavior. It does not reinterpret existing
Store, region, cell, effect or cleanup ownership. Shared process address space
does not itself grant Ash authority, cross-thread representation safety or
visibility. The exact source surface is not yet selected; accepting this
contract does not accept a syntax or an implementation-specific magic name.

## Affected specification areas

The completed change must update [static semantics](../../spec/static-semantics.md#scoped-retained-control),
[dynamic semantics](../../spec/dynamic-semantics.md#scoped-retained-control-execution),
[elaboration and independent validation](../../spec/elaboration.md#validation-boundary),
and the specification index for any new surface and runtime operations. It must
also update applicable resource, foreign and cleanup sections when the actual
representation is selected. No new protocol checker is proposed.

## Resulting specification truth

When implemented, reviewed, verified and integrated into Main, admitted worker
entries and copied channels obey the rules above. This proposal alone changes
no current language truth; it does not prove native code correct.

## Interactions

[CP-0028](CP-0028-checked-functional-network-ledger.md) describes the
ordinary Work/Ack program and its intended register-before-publication,
coverage and drain behavior. The application program is not certified by the
transport. [N5](https://github.com/dikini/ash-lang/issues/80) includes producing
cleanup and settlement. Neither a local empty Store nor application bytes
certifies transport End or network settlement.

## Non-goals

No shared mutable application resources, arbitrary closure or endpoint transfer,
zero-copy, process containment, general message graph copying, worker recovery,
native-stack suspension, general proof language, scheduling fairness, deadlock
freedom, termination, or proof of native memory safety is introduced.

## Required evidence

The contract and host candidate were independently reviewed at the head above.
The product must
test admitted and rejected entry captures and evidence, foreign-pointer and
resource escape, full and closed sends, failures on both sides of each commit,
FIFO with accepted pending work, visibility, receive allocation failure,
registration races and stale notifications, genuine versus false `End`, and
release with outstanding waiters and backing users. Include capacity-one feedback
and producing cleanup, normal and abandonment paths, actual native observations
and separately labelled injected failures. Establish local ownership, FIFO, worker lifetime, failure retention and actual
settlement for the revised implementation; distinguish transport receipt from
application processing. Existing N2 model and per-message checker evidence
retains only its original scope. Generic control and final gates remain; see
[TASK-0058](../tasks/TASK-0058-pinned-worker-network.md).
