# AD-0017: Pinned worker host and transport

- ID: `AD-0017`
- Status: accepted
- Related: [CP-0027](../proposals/CP-0027-pinned-workers-and-copied-channels.md), [DN-0058](../design/DN-0058-pinned-worker-host-and-channel.md), [TASK-0058](../tasks/TASK-0058-pinned-worker-network.md)

## Decision

Run the fixed two-worker network on two host threads, each with a separately
constructed Ash root, executor and local Store. A worker remains on its carrier
thread for its execution; CPU affinity is not required. The enclosing network
owner retains both workers and two dedicated positive-capacity FIFO channels,
one in each direction, through actual endpoint and backing settlement.

Transport copies finite bytes into channel-owned storage before an atomic
acceptance/publication, and reconstructs bytes in the receiver's selected region
before committing receipt. Source and destination roots remain independent.
Application and control envelopes share each direction's FIFO but carry an
authenticated kind and sending side. Host operations authenticate transport
origin only: ordinary linked Ash implements the ledger, acknowledgements and
drain, and the separately accepted checker must reconstruct their relationships.
The host does not certify ledger correctness, decode completion facts, or own
another worker's retained control.

Use synchronized state changes and level-triggered wait registration with an
atomic readiness recheck. Readable includes a message, genuine End and failure;
Writable includes a send attempt, Closed and failure. A registration that sees
an already-ready or terminal state queues a wake without needing a later edge.
Each wake names a generation-checked local registration; the owning executor
rechecks the state and restores its own continuation. No callback or registration
may outlive its protected support. Complete or join owned carriers and exclude
future users before release; terminal failure may report incomplete teardown.

This non-language choice does not make the proposed semantics current Ash.
The accepted transition and its entry, operation and failure contracts are in
[CP-0027](../proposals/CP-0027-pinned-workers-and-copied-channels.md).

## Context

[DN-0055](../design/DN-0055-algebra-of-regions-lifetimes-and-ownership.md)
distinguishes copying from shared access and region transfer. Copying an
ordinary handle or pointer would not establish independent ownership or
cross-thread visibility. [DN-0056](../design/DN-0056-scoped-continuation-retention-and-library-scheduling.md)
requires each Store's actual control and cleanup to remain owned locally, and
separates application quiescence from endpoint and backing settlement.
[DN-0058](../design/DN-0058-pinned-worker-host-and-channel.md) compares copied
bytes, transferable message regions and shared graphs. The first choice avoids
new region transfer and shared-heap contracts while allowing typed request/reply
codecs and local retained computations. It imposes copy cost and still requires
transport, control-origin and completion evidence.

An independent review of the contract and this decision candidate found no
actionable findings at `b296e17ce9e4f1760ce73df4f4716ef0c0fb2093`; that review
did not establish product, native or proof gates. The host's native bindings
remain ordinary slim-FFI module assumptions, including any concurrent access to
shared native state. Separate Ash roots do not prove those assumptions.

## Consequences

Each worker initializes its own global records and selected evidence from
admitted linked code. Immutable code metadata may be shared only when its actual
representation permits concurrent access. The host synchronizes transport and
notification boundaries; it does not add synchronization to ordinary Store
operations or transfer their keys. Bounded feedback requires the local executor
to keep receiving and servicing control while application work waits.

No endpoint migration, general graph transfer, worker recovery, native-stack
suspension, process containment, fairness, deadlock freedom, termination or
proof of native memory safety follows. Application bytes and copied identifiers
cannot authenticate a completion or control envelope. The protocol checker must
validate actual linked code and reject bypasses before completion analysis uses
these transport facts.

## Verification

Before release relies on this decision, establish the bounded worker/channel
preservation assignment and its correspondence to actual host and evaluator
behavior. Exercise entry and capture rejection, partial startup, failures around
commit, capacity-one FIFO and visibility, receiver allocation failure,
registration/poll/cancel races, stale wakes, terminal late registration, genuine
End and settlement with outstanding callbacks. Separate actual native
observations from injected failure evidence and state Rust/OS assumptions.
The N3 finite-ledger proof and linked-Core checker have separate contracts and
gates; N-core, N-proof and N-final remain required under
[TASK-0058](../tasks/TASK-0058-pinned-worker-network.md).
