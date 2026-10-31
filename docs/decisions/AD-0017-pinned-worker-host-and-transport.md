# AD-0017: Pinned worker host and transport

- ID: `AD-0017`
- Status: accepted
- Related: [specification](../../spec/README.md), [DN-0058](../design/DN-0058-pinned-worker-host-and-channel.md)

## Decision

Run the fixed two-worker network on two host threads, each with a separately
constructed Ash root and executor. Local Stores remain on that carrier. A worker remains on its carrier
thread for its execution; CPU affinity is not required. The enclosing network
owner retains both workers and two dedicated positive-capacity FIFO channels,
one in each direction, through actual endpoint and backing settlement.

Transport copies finite bytes into channel-owned storage before an atomic
acceptance/publication, and reconstructs bytes in the receiver's selected region
before committing receipt. Source and destination roots remain independent.
Application and control envelopes share each direction's FIFO but carry an
authenticated kind and sending side. Host operations authenticate transport
origin only: ordinary Ash implements the ledger, acknowledgements and drain
with ordinary error handling. The host does not certify ledger correctness,
decode completion facts, or own another worker's retained control. The user
superseded the earlier protocol-specific compiler checker on 2026-10-31. The
ordinary protocol and host behavior are integrated into Main; the
[delivery record](https://github.com/dikini/ash-lang/issues/55) states its scope.

Use synchronized state changes and level-triggered wait registration with an
atomic readiness recheck. Readable includes a message, genuine End and failure;
Writable includes a send attempt, Closed and failure. A registration that sees
an already-ready or terminal state queues a wake without needing a later edge.
Each wake names a generation-checked local registration; the owning executor
rechecks the state and restores its own continuation. No callback or registration
may outlive its protected support. Complete or join owned carriers and exclude
future users before release; terminal failure may report incomplete teardown.

### Terminal failure retention clarification

When terminal failure prevents checked local completion, the affected worker's
carrier retains its interrupted evaluator, local heap, frames, native binding
support and outstanding delivery obligations on that same carrier for the
remaining process lifetime. It reports incomplete teardown to the coordinator;
that report carries accounting, not the worker's Store or permission to release
backing. The host marks the shared transport terminal and retains its support.
The holder does not execute Ash, restore or transfer continuations, retry work,
run cleanup on the coordinator, or assert successful settlement. Ordinary host
waiting keeps the carrier alive; it does not capture a resumable native stack.
Process death is outside this decision's containment guarantee.

The failure boundary must preserve the holder on reported runtime failure,
including in-progress reservations, callbacks, region providers, retained
control and native binding support. The admitted native binding contract must
state whether unwinding is supported. An unknown panic cannot establish
completion or successful settlement; containment of arbitrary native behavior
and process death are outside the decision. An implementation must not claim
panic recovery unless its actual boundary preserves the affected support.

This non-language choice does not itself define Ash semantics. The entry,
operation and failure contracts are in the [specification](../../spec/README.md).

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
cannot authenticate a completion or control envelope. The ordinary protocol
program handles its data; existing generic retained-control and host settlement
contracts remain separate and are not discharged by a protocol result.

## Verification

Verify actual host and evaluator behavior with the required tests. Earlier
worker/channel and one-way models are conditional historical evidence, not a
proof of the current carrier or ordinary protocol. Retained M1–M3 generic
ownership and drain-safety evidence keeps its original scope; generic C3
regressions remain separate. Exercise entry and capture rejection, partial
startup, failures around
commit, capacity-one FIFO and visibility, receiver allocation failure,
registration/poll/cancel races, stale wakes, terminal late registration, genuine
End and settlement with outstanding callbacks. Separate actual native
observations from injected failure evidence and state Rust/OS assumptions.
Earlier N3 ledger and checker evidence retains its original scope; it is not
evidence of the ordinary protocol program. The historical
[TASK-0058](https://github.com/dikini/ash-lang/blob/b5c62bf25b87bc1c2ce9f87e4efc3ca0e0107c9a/docs/tasks/TASK-0058-pinned-worker-network.md) records the delivery and its separate evidence.
