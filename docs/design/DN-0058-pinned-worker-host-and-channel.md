# DN-0058: Pinned worker host and channel

- ID: `DN-0058`
- Status: exploring
- Related: [AD-0017](../decisions/AD-0017-pinned-worker-host-and-transport.md), [CP-0027](../proposals/CP-0027-pinned-workers-and-copied-channels.md), [DN-0055](DN-0055-algebra-of-regions-lifetimes-and-ownership.md), [DN-0056](DN-0056-scoped-continuation-retention-and-library-scheduling.md), [TASK-0058](../tasks/TASK-0058-pinned-worker-network.md)

This note retains the exploration and proof questions behind the accepted
[AD-0017](../decisions/AD-0017-pinned-worker-host-and-transport.md). It is
informative, does not establish current Ash behavior, and does not itself
authorize implementation. The semantic transition belongs in CP-0027.

## Reviewed decision candidate

Use two host threads, each running one local Ash executor and owning its Store.
An enclosing host network owner creates two dedicated, positive-capacity FIFO
channels, one in each direction, and retains their backing through settlement.
Each channel has exactly one send and one receive authority. Only copied finite
bytes and private authenticated protocol envelopes cross the boundary. The
receiver constructs local data; no sender-local graph is shared or moved.
Synchronization belongs at publication, receipt, wait registration and support
settlement. Ordinary local Store operations remain worker-local. Use kernel
thread identity for affinity; CPU affinity is neither needed nor promised.

Entry preparation creates support and checks the closed function and startup
inputs before launching an admitted entry. The implementation must provide a
single observable entry commit, protect all owned support across that transition,
and distinguish launch failure before commit from terminal failure afterward.
It must not run or abandon worker-owned Ash cleanup on another thread. A failed
launch, including a partially created peer, needs an explicit joined/settled or
incomplete-teardown result; it cannot report a successfully closed network
while a carrier or callback may still access support.

The host may implement each queue with a mutex and condition variable or another
equivalent synchronization mechanism. Under the same synchronization, observe
the predicate, register a waiter and recheck before parking; wake and recheck
when publication, capacity, seal or failure changes the predicate. Every native
access and notification retains support until actually finished. A generation
or equivalent non-reused identity ties a notification to its current local wait;
exhaustion fails rather than making stale identity current. Uncertain acceptance
is distinct from definite refusal: retain its reservation and support, and do
not retry or retire it without an authenticated resolution. Join or an equivalent
actual completion acknowledgement is required before destroying owned threads
and backing. Queued callbacks and registered waiters count even when no worker
is currently running, and settlement must exclude any future callback or wake
against that activation.

Readiness includes terminal observations: Readable covers a message, genuine
End or receive failure; Writable covers an admissible send attempt, Closed or
send failure. Only Empty and Full respectively park. Registration after seal or
failure must enqueue the corresponding wake during its recheck, even if no
later event occurs. Exercise that schedule as well as publication/registration,
poll and cancellation races in the host evidence.

Application and protocol messages have distinct, private representations. A
peer identity comes from the actual channel direction, not a payload field.
Only the protocol driver can emit or consume control envelopes. No ordinary
byte sequence, copied identifier, or foreign callback can assert completion.
The host contract must preserve their separation even when payload bytes are
arbitrary. Interpreting bytes as an address does not grant pointer validity or
resource authority; workers must not use such an address to recover sender-local
ownership. The implementation must authenticate actual message kind and origin,
not rely on a source type annotation alone.

## Why this choice

The current retained-control execution gives each Store exclusive ownership of
its slots and tracks actual suffix and cleanup completion. DN-0056's local
drain transfers only within that execution. Kernel preemption preserves the
carrier's state; it does not establish an Ash scheduling boundary. DN-0055's
channel comparison distinguishes placement, resource authority and backing
lifetime. A copy is useful only if actual representation and visibility are
safe at the destination; copying a handle or a pointer does not achieve that.

Compare three choices:

| Choice | Benefit | Obstacle in this milestone |
| --- | --- | --- |
| Dedicated channels with copied bytes | Simple ownership and explicit synchronization; fits ordinary encoding and local regions. | Copy and bounded capacity cost; requires accounting and authenticated control. |
| Transfer message regions or closures | Can avoid a copy. | Needs a new ownership scheme, access revocation, captures, affinity and completion handoff. |
| Shared heap or general shared immutable graphs | Can reuse existing data. | Needs representation, lifetime, concurrent access and reclamation rules; immutability alone is insufficient. |

The first choice fits the stated two-worker scenario without committing Ash to
the other ownership schemes. A byte-only boundary also avoids assuming that
all values of a structurally similar type are resource-free: the actual copied
representation is finite bytes, and admission of entry authority is checked
separately. A private control channel or tagged envelope must still provide
authenticated provenance; bytes alone do not prove protocol facts.

This is a bounded representation choice rather than a fixed application
protocol. Ordinary typed codecs can encode request/reply values and finite-list
ledger metadata as bytes and reconstruct local values at the receiver. Retained
computations and resource-owning regions remain on their worker. The N6 example
must demonstrate that composition and the SQLite canary; transparent transport
of arbitrary resource-free graphs is deliberately not promised here. If the
actual example requires that promise, revisit the semantic proposal.

## Proof and verification obligations

The worker/channel preservation assignment is bounded to two fixed workers,
two dedicated FIFO directions, positive finite capacities and finite traces.
Model entry preparation/commit/failure, local step and preemption, send
preparation/acceptance/publication/failure, receive preparation/commit/failure,
seal/End, waiter registration/wake/staleness, and endpoint/backing settlement.
Prove that each step preserves unique local Store ownership, no gap in delivery
and backing coverage, the FIFO equation and capacity bound in CP-0027, no false
End, and no release while any admitted operation or notification can access
support. Include partial setup and terminal failure. Identify assumptions at
the Rust/OS boundary and test the actual implementation against them. These
finite safety results establish neither scheduling progress nor termination.

N3 has four distinct bounded assignments:

1. Prove finite ordered whole-entry removal, `Found` exactly on membership,
   uniqueness and frame properties, then initialization, registration,
   closure, retirement and matching, wrong-peer, unknown and duplicate
   acknowledgements preserve local invariants and non-reused freshness.
2. Under explicit actual-completion and faithful transport premises, prove
   rooted coverage from reservation through pending publication, receipt and
   dispatch, and from closed childless retirement through acknowledgement and
   matching removal. Induct over finite traces. Stable AppQuiet additionally
   needs closed admission and producer premises; backing settlement is separate.
3. Prove the restricted checker rules sound against modeled evaluation: all
   reachable selected branches and returns, actual nominal identities, verified
   equality and pure callees, finite proper-tail recursion, helper premises and
   acyclic dependencies. A proof of a standalone removal function is not a proof
   of checker soundness. The checker must bind its untrusted plan to the actual
   linked body and independently revalidate supported transformed/imported Core.
4. Establish current-successor flow and invalidation, including no-op equality,
   stale or reentrant state and actual completion. Unsupported transformations
   must preserve a checkable form or reject; cumulative budget exhaustion grants
   no partial fact or release permission.

Finiteness cannot be inferred merely from a recursive Ash data type, because
cyclic data is admitted. Existing [retained-control evidence](retained-control/README.md)
establishes bounded local results under its stated premises, not network or
Rust/evaluator correctness. N4 composes the new results with actual local
completion and authenticated transport; N5 uses that composition before
settlement. The worker model is not a proof of the ledger or native memory.

Evidence includes adversarial stale notification, false `End`, send/receive
failure on each side of a commit, publication ordering under capacity pressure,
visibility and no lost wakeup, plus the source/Core admission and revalidation
cases in CP-0027. Native tests observe actual host behavior but do not prove
all schedules or the correctness of external code. Record independent review,
fixed source/configuration pins and residual assumptions before adoption.

## Implementation correspondence

Implementation must verify CP-0027's entry and operation signatures, private
control-envelope origin, error cases and post-entry failure against actual
linked definitions. In particular, verify startup snapshots, level-triggered
waits and the N3/N4 boundary that admits only checked ordinary Ash driver paths
to control emission. If these cannot be expressed as accepted, return to the
proposal rather than silently widening authority.
