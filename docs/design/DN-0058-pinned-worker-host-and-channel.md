# DN-0058: Pinned worker host and channel

- ID: `DN-0058`
- Status: accepted
- Related: [AD-0017](../decisions/AD-0017-pinned-worker-host-and-transport.md), [DN-0055](DN-0055-algebra-of-regions-lifetimes-and-ownership.md), [DN-0056](DN-0056-scoped-continuation-retention-and-library-scheduling.md), [historical TASK-0058](https://github.com/dikini/ash-lang/blob/b5c62bf25b87bc1c2ce9f87e4efc3ca0e0107c9a/docs/tasks/TASK-0058-pinned-worker-network.md)

## Accepted and implemented

The fixed two-worker host and copied FIFO byte channels are accepted and
implemented on `main` as part of `ffi-ash`. [AD-0017](../decisions/AD-0017-pinned-worker-host-and-transport.md)
records the architecture. The [static](../../spec/static-semantics.md#pinned-worker-networks)
and [dynamic](../../spec/dynamic-semantics.md#pinned-network-execution)
specifications define the language contract.

| Capability | Status |
| --- | --- |
| Two host threads, each with an independent Ash root and executor | Implemented |
| Worker-local Stores and retained continuations | Implemented |
| Positive-capacity copied FIFO byte channel in each direction | Implemented |
| Application/Control envelope kinds and channel-authenticated sending side | Implemented |
| Send/receive preparation, copied receipt, seal/End and endpoint settlement | Implemented |
| Generation-checked watches, readiness rechecks, poll and cancellation | Implemented |
| Same-carrier retention after terminal failure | Implemented |
| Ordinary Ash Work/Ack driver, codec and error handling | Implemented |
| Generated executable images containing Network operations | Not implemented |
| Worker migration, transferred regions, shared graphs and shared Stores | Not implemented |
| Protocol-specific compiler checker and one-way completion checker | Retired |

## Accepted design

Each worker remains on its carrier thread and initializes its own Ash root.
CPU affinity is not required. Store slots and continuations remain local to
their worker. The enclosing network owner retains both carriers and channel
backing through settlement.

Worker entries are closed named top-level functions. Admission checks their
linked definitions, effects, dependencies and captures. Startup inputs are
copied. A caller-owned closure, Store, cell, region or provider is not transferred.

Send copies finite Bytes into channel-owned storage before acceptance. Receive
reserves the FIFO head and constructs the receiver's complete result in its
selected region before removing the message. A failed construction restores
the head. Application and Control envelopes share each direction's FIFO.

The channel authenticates message kind and sending side. Ordinary Ash code can
call `send_control`; the compiler does not require a special protocol driver or
certify acknowledgements, ledger invariants or per-message processing. The
[ordinary protocol](../../libraries/network_protocol.ash) owns those checks and
error paths.

`finish_send` seals the sending polarity. `End` follows seal and the accepted
queue's exhaustion. `finish_receive` requires the actual incoming channel to be
sealed and empty with no outstanding transport operation. Transport End does
not establish application processing or cleanup completion.

Watch registration rechecks readiness atomically with registration. Readable
includes message, End or failure; writable includes send capacity, Closed or
failure. Wakes identify generation-checked registrations and require a new
state check. Store restoration remains local to its owning executor.

Returned workers retain their roots, evaluators and bindings on their carriers.
After observing both normal returns, finished endpoints, completed operations
and removed registrations, the coordinator authorizes carrier-local teardown.
Settlement then joins the carriers and releases backing after that teardown
completes.

## Why this choice

Copied bytes give each receiver independently owned storage. They require no
region transfer, shared ordinary heap or continuation migration. A mutex
protects transport state; ordinary Store operations remain local.

## Proof and verification obligations

[Public worker tests](../../tests/pinned_network.rs),
[transport tests](../../src/eval/network_transport.rs) and
[carrier tests](../../src/eval/machine.rs) cover copied delivery, bounded FIFO
state, readiness, failure and settlement. [Scheduling tests](../../tests/scheduling.rs)
exercise worker-local control policies. The
[library guide](../../libraries/README.md) records ordinary protocol execution
and the generated-image limitation.

The [worker/channel model](retained-control/worker-channel-correspondence.md),
[ledger model](retained-control/network-ledger-correspondence.md) and
[one-way model](retained-control/one-way-completion-correspondence.md) retain
historical conditional proof results. The earlier protocol-specific checker
requirements were superseded on 2026-10-31 and are retired.

## Terminal failure holder

After terminal failure prevents checked local completion, the affected carrier
retains its interrupted evaluator, heap, frames, bindings and outstanding
support for the remaining process lifetime. It reports incomplete teardown.
The holder executes no Ash, retries no work and moves no continuation to the
coordinator. The host marks transport terminal and retains its support.

## Not implemented

Worker migration, region ownership transfer, shared ordinary graphs, shared
Stores, worker recovery and Network private-image encoding are not implemented.
The implementation supplies no fairness, deadlock-freedom or termination guarantee.
