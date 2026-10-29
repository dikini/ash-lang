# CP-0027: Pinned workers and copied channels

- ID: `CP-0027`
- Status: proposed
- Related: [DN-0055](../design/DN-0055-algebra-of-regions-lifetimes-and-ownership.md), [DN-0056](../design/DN-0056-scoped-continuation-retention-and-library-scheduling.md), [DN-0058](../design/DN-0058-pinned-worker-host-and-channel.md), [TASK-0058](../tasks/TASK-0058-pinned-worker-network.md)

> This proposal is not current Ash. It does not authorize product work until
> its contract and required evidence have been independently reviewed and accepted.

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

### Concrete entry and endpoint candidate

This review delta proposes a specific representation; it is not accepted and
does not define current Ash. The defining identities below belong to a new sealed
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
| `send_control(worker, bytes)` | Sends a control envelope using the same queue, commit and failure rules as `try_send`; only the checked protocol driver may invoke it. |
| `finish_send(worker)` | Irreversibly seals this send polarity after earlier operations resolve. |
| `finish_receive(worker)` | Completes the receive polarity only after genuine End and checked actual completion of earlier processing and required local cleanup. |
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
The recheck queues a pending wake for the returned generation before `watch`
returns if the predicate is already ready. `poll_wake` removes at most one
pending wake and readiness is level-triggered: if the registration remains
active and the predicate remains ready, another wake is pending or is queued
before the executor parks. Successful cancellation prevents new wake issuance;
previously queued wakes for the invalidated generation are harmless. Test the
publish-before-register, register-before-publish, poll-before-publish,
readiness-between-recheck-and-park, and cancel-versus-publish schedules.
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
the request cannot establish that association. The linked validator admits
`send_control` only on the designated ordinary Ash protocol-driver path whose
actual body, callers and transitive captures are checked under N3/N4; source
application paths cannot call it or access the raw endpoint. The host checks the
sealed operation identity and side, but does not interpret the control bytes.
Registration, ledger transition, local completion, acknowledgement
and application-drain control remain ordinary linked Ash definitions checked
under N3/N4. The checker must reconstruct their actual relationships and prove
the codec correspondence for identifiers; the host does not certify the ledger
or assert completion merely because it emitted an envelope.
For N4, access to raw application publication must be confined to the checked
driver path; analysis follows actual calls, captures and selected evidence through
imports to reject bypasses. A `finish_receive` call likewise cannot obtain
permission from an ordinary Boolean or a runtime claim that processing finished:
the actual local Store and required suffixes must have completed under the
accepted completion analysis.

Lower acquisition to an explicit Core network owner carrying the fresh identity,
resolved entry binders and instantiations, capacity and startup operands. Lower
operations to sealed, identity-indexed Core operations with the actual
activation and injected side, and explicit normal and terminal-failure paths.
Independent linked Core validation reconstructs the entry definitions, type and
row instantiations, selected evidence, admitted captures and services, side and
lexical owner. It checks normal and abandoned close predecessors and authentic
result/state relationships; source summaries, names, serialized origin claims
and same-typed operations grant no authority. Imports and transforms must leave a
reconstructible form or reject. The separate N3 contract must define how the
restricted checker validates the ordinary ledger and its control dependencies.

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
representation must preserve these defining identities and behavior. Independent
review and acceptance of this complete candidate, the host decision, and its
proof assignments still precede product work.

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
Once receipt commits, later processing and cleanup remain receiver obligations.

The abstract accounting is `accepted = received ++ queued ++ pending`, in
acceptance order, with `length(queued) + length(pending) <= capacity`. The
implementation may make acceptance and publication one atomic transition; it
must still preserve the pending-state obligation if it separates them. It must
not allow later publication or `End` to overtake an earlier accepted send.
There is no implicit discard or redelivery. If failure prevents the normal
policy of processing all accepted messages, the network reports terminal
failure and retains or disposes support only under an explicit failure contract;
it does not claim successful drain.

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
the sender finishes; its local completion also waits for processing, handler
suffixes and cleanup, including any retained work.

Backing may be released only after both endpoint completions and all pending
operations, wait registrations, callbacks, notifications and other backing
users have actually settled, and no future callback or wake can be issued
against that activation. A worker's local quiescence, receipt of `End`, or
an application-quiescence observation alone is insufficient. Normal and
abandoned exits require separate checked completion paths; an unprovable close
is rejected. Terminal failure may leave support unreleased and cannot turn an
unproved close into a release permission.

## Semantic delta

The proposal adds admitted worker entry, dedicated copied transport, and
authenticated endpoint and completion facts. It does not reinterpret existing
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
representation is selected. A later checker proposal must govern N3/N4 facts.

## Resulting specification truth

When implemented, reviewed, verified and integrated into Main, admitted worker
entries and copied channels obey the rules above. This proposal alone changes
no current language truth; it does not prove native code correct.

## Interactions

The [N3 issue](https://github.com/dikini/ash-lang/issues/78) requires a separate
finite-list ledger proof and restricted checker. For bidirectional work, a child
is registered before publication, and its parent remains covered until an
authentic acknowledgement. A reply delivered to an already covered continuation
must not create a causal cycle. [N4](https://github.com/dikini/ash-lang/issues/79)
must reconstruct these facts on actual linked Core before release, and
[N5](https://github.com/dikini/ash-lang/issues/80) must first seal fresh roots
while allowing covered descendants, then settle service, endpoints and backing.
Neither a local empty Store nor an application payload certifies network drain.

## Non-goals

No shared mutable application resources, arbitrary closure or endpoint transfer,
zero-copy, process containment, general message graph copying, worker recovery,
native-stack suspension, general proof language, scheduling fairness, deadlock
freedom, termination, or proof of native memory safety is introduced.

## Required evidence

Independent contract and proof review must precede acceptance. The product must
test admitted and rejected entry captures and evidence, foreign-pointer and
resource escape, full and closed sends, failures on both sides of each commit,
FIFO with accepted pending work, visibility, receive allocation failure,
registration races and stale notifications, genuine versus false `End`, and
release with outstanding waiters and backing users. Include capacity-one feedback
and producing cleanup, normal and abandonment paths, actual native observations
and separately labelled injected failures. Prove bounded preservation of local
ownership, delivery coverage, FIFO and settlement for every transition before
using those facts for release. The N3 proof and checker, N-core, N-proof and
N-final gates remain separate; see [TASK-0058](../tasks/TASK-0058-pinned-worker-network.md).
