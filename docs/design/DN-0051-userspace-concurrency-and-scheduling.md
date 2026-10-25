# DN-0051: Userspace Concurrency and Scheduling

- ID: `DN-0051`
- Status: exploring
- Related: [DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md),
  [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md),
  [DN-0044](DN-0044-no-default-runtime.md),
  [DN-0045](DN-0045-native-compilation-and-interactive-execution.md),
  [DN-0048](DN-0048-pure-core-kernels-and-parallel-lowering.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This note records research and candidate future directions. Current Ash is
> intentionally sequential and remains the stabilization target. This note
> changes no specification, implementation, accepted architecture, proof scope,
> or stabilization criterion. It authorizes no prototype or implementation.

Research reviewed on 2026-10-16. Here, userspace means execution managed within
Ash above kernel threads and events. Browser execution is not a requirement
of this investigation.

## Question

What public contracts and implementation approaches could later give Ash
asynchronous operations, concurrent tasks, and multicore execution with useful
latency, throughput, and capacity behavior?

There are three distinct goals:

- Asynchrony lets an operation remain pending without occupying its worker.
- Concurrency lets several computations make progress during overlapping
  lifetimes, possibly on one worker.
- Parallelism executes work simultaneously on multiple workers or devices.

Kernel threads and I/O events supply mechanisms. They do not decide who owns
an Ash task, how a suspended handler retains its context, when cancellation
finishes, or whether a value may cross a worker boundary.

Research can proceed independently of sequential stabilization. Future semantic
changes need their own proposal and task after the relevant sequential boundary
is stable. No current representation or ABI needs reserved task machinery.
Existing sequential conformance evidence should remain a comparison baseline;
it is not evidence of concurrent safety or scheduler performance.

## Context

The [dynamic semantics](../../spec/dynamic-semantics.md) define one deterministic
small-step configuration. An operation moves a continuation segment into its
selected clause; resumption restores its lexical handler nesting and eventually
returns to remaining clause work. It does not copy that segment.

The [static continuation rules](../../spec/static-semantics.md#effects) require
exactly one resume or checked discard on each normally completing clause path.
The hidden capability has no source type or binder. It cannot enter a closure,
argument, result, or queue. Consequently, current source handlers cannot retain
a continuation and resume it later from a scheduler. An explicit library state
machine is possible in principle, but does not provide transparent suspension
through ordinary calls.

[Resource dependencies](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
and [cleanup](../../spec/dynamic-semantics.md#scoped-cleanup-actions) already
separate reusable access from completion ownership. Capture moves ownership;
discard closes owned captures while preserving required outside and running
completion. These rules motivate future suspension contracts, but do not already
establish cancellation, thread transfer, or race freedom.

[AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md) supplies inspectable
control independent of the Rust call stack. Its deep-expression evidence does
not measure native task switching. [DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md)
separately explores bounded transfer and asynchronous hooks. Its async sketch
does not establish fairness, parallel execution, or latency, and its retained
one-shot proof work does not prove suspension or escaping control. Structural
consumption schedules in that experiment are not a userspace task scheduler.

There are two further boundaries:

- [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md) explores
  access and usage properties under sequential assumptions; it establishes no
  concurrent memory model.
- [DN-0048](DN-0048-pure-core-kernels-and-parallel-lowering.md) explores parallel
  implementation of checked pure kernels without introducing source
  concurrency. It remains a separate throughput route.

## Constraints

These are criteria for comparing future candidates, not additions to current
stabilization requirements:

- Preserve the stabilized sequential behavior of code outside the extension.
- Retain unique control ownership, exact interpretation, resource dependencies,
  and required completion through suspension and lowering.
- State progress, capacity, foreign, and sharing assumptions explicitly.
- Compare end-to-end latency, throughput, and retained memory under the same
  workload; do not infer performance from API shape or queue microbenchmarks.

## Lessons from current practice

Public lifetime semantics and internal scheduling are independent choices.
Structured concurrency gives children an owner and a completion boundary. It
does not itself provide preemption, overload control, or multicore safety.

| Approach | Useful precedent | Cost or limitation |
| --- | --- | --- |
| Effect-based direct-style tasks | OCaml Eio uses switches for fiber/resource lifetimes and separate domains for parallel execution. | Local fibers cooperate; a long computation can monopolize its domain. |
| Stackless futures | Rust separates pending computations from spawning tasks; Tokio supports local and work-stealing execution. | Suspension state and cancellation safety need careful lowering. Long polls obstruct fairness. |
| Managed green threads | Go provides direct-style goroutines, small growable stacks, and managed-code preemption. | The runtime/compiler commitment is larger. Goroutine creation alone supplies no structured lifetime. |
| Virtual threads | Java can suspend many direct-style I/O requests over fewer carrier threads. | More outstanding requests improve throughput only when downstream capacity permits; native boundaries still matter. |
| Actors and supervision | Erlang isolates service state through processes and messages and contains failures through supervision. | Mailboxes still need overload protocols. Service supervision and request-scoped joining solve different problems. |
| Per-core ownership | Seastar keeps data local and makes remote execution explicit. | Partitioning can reduce synchronization but exposes imbalance and cross-core coordination. |
| Composable operation protocols | C++ P2300 distinguishes schedulers, operation state, and value/error/stopped completion. | This is a useful low-level boundary, not a reason to expose its template vocabulary in Ash. |

Primary sources: [Eio](https://github.com/ocaml-multicore/eio),
[Rust Future](https://doc.rust-lang.org/std/future/trait.Future.html),
[Tokio runtime](https://docs.rs/tokio/latest/tokio/runtime/index.html),
[Go runtime architecture](https://go.dev/src/runtime/HACKING),
[Go preemption](https://go.dev/src/runtime/preempt.go),
[Java virtual threads](https://docs.oracle.com/en/java/javase/27/core/virtual-threads.html),
[Erlang processes](https://www.erlang.org/doc/system/ref_man_processes.html),
[Seastar](https://seastar.io/shared-nothing/), and
[P2300R10](https://www9.open-std.org/JTC1/SC22/WG21/docs/papers/2024/p2300r10.html).

Two distinctions deserve explicit attention. Swift structured task groups do
not make cancellation forceful; cancellation remains cooperative. Actor
isolation also permits interleaving across suspension, so it does not preserve
an entire asynchronous operation's invariant automatically.
[Structured concurrency](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0304-structured-concurrency.md),
[actor reentrancy](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0306-actors.md).

Java 27 was released on September 15, 2026, but its structured concurrency API
is still preview. Its scope close waits for subtasks, including those that
ignore interruption. A timeout can therefore precede actual scope completion.
This is a useful contract to study, not an API maturity claim to copy.
[Release announcement](https://blogs.oracle.com/java/the-arrival-of-java-27),
[StructuredTaskScope](https://docs.oracle.com/en/java/javase/27/docs/api/java.base/java/util/concurrent/StructuredTaskScope.html).

## Candidate directions

Compare public task semantics, suspended-control representation, and placement
policy separately. A choice on one axis does not settle the others.

### Public task and lifetime contract

The strongest candidate for later investigation is structured, one-shot tasks
with effect-based suspension. A parent scope owns children and retained support
until they finish. Pending work can relinquish its worker without requiring a
general first-class continuation API or multi-shot control.

This is a research preference. Current Ash has no such task contract.
[DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md) offers a useful
bounded alternative to arbitrary escape: transfer into an owner whose input,
answer, support, interpretation, and completion policy are fixed. Its feasibility
and interaction with source handlers remain open.

A future implementation would need to preserve the entire suspended task state,
including clause work after resume and required completion outside a captured
segment. Merely placing the selected continuation suffix in a queue is
insufficient. Starting a child would create fresh control with admitted captures;
it would not clone the parent's continuation.

An ordinary closure does not capture the surrounding handler stack. Child-task
interpretation therefore needs a separate contract: explicitly supplied context,
restricted inherited interpretations, or checked capture at task creation. Live
completion owners and mutable handler state cannot be copied indiscriminately.

### Representation of suspended control

| Representation | Potential advantage | Main comparison question |
| --- | --- | --- |
| Explicit library state machines | Small semantic commitment; useful for an explicit polling API. | Is manual state management acceptable for the intended applications? |
| Compiler-generated state machines or selective CPS | Store live state at suspension; retain direct calls where justified. | What are frame size, allocation, dispatch, code-size, and higher-order-call costs? |
| One-shot stackful fibers | Preserve nested direct-style calls; detach and relink control segments. | What are stack storage, growth, unwinding, foreign-frame, and target costs? |

Rust describes generated async state as roughly an enum retaining live values at
each suspension. Its pinning contract illustrates a general obligation: references
into suspended state and intrusive registrations need stable storage and correct
destruction. Ash need not expose Rust's `Pin` API to meet that obligation.
[Async blocks](https://doc.rust-lang.org/reference/expressions/block-expr.html#async-blocks),
[Pin](https://doc.rust-lang.org/std/pin/index.html).

OCaml uses one-shot effect continuations and stack segments. It also prohibits
effects escaping through certain C callback boundaries. Stackful execution does
not make arbitrary foreign frames suspendable. Its implementation paper provides
bounded benchmark evidence, not a universal performance ordering against CPS.
[OCaml effects](https://ocaml.org/manual/5.5/effects.html),
[Retrofitting Effect Handlers onto OCaml](https://anil.recoil.org/papers/2021-pldi-retroeff.pdf).

Koka demonstrates effect-handler compilation through evidence passing and yield
propagation to ordinary C. It supports comparing selective control lowering with
stack switching; it does not predict Ash's costs. LLVM supplies several coroutine
lowerings, but choosing an intrinsic does not choose ownership, cancellation, or
the scheduler ABI.
[Generalized Evidence Passing](https://www.microsoft.com/en-us/research/publication/generalized-evidence-passing-for-effect-handlers-or-efficient-compilation-of-effect-handlers-to-c/),
[LLVM coroutines](https://www.llvm.org/docs/Coroutines.html).

### Placement and scheduling policy

Three policies are worth comparing independently of representation:

1. A local cooperative event loop: simplest control and affinity boundary; no
   multicore speedup and no protection against an unbounded running task.
2. A worker pool with local queues and work stealing: general load balancing;
   migration requires checked transportability and incurs synchronization costs.
3. Per-core task/data ownership with explicit remote messages: useful for
   partitionable services; persistent skew and coordination need explicit policy.

Compiler checkpoints or managed preemption can supplement the first two. They
are not free consequences of effects. Go's safe points require runtime/compiler
cooperation; Tokio's fairness contract instead assumes bounded task count and
bounded poll duration. Neither supplies a hard real-time guarantee.

## Candidate API contracts to investigate later

These names describe concepts, not proposed Ash syntax or current library APIs.
The [concrete local sketch](#concrete-local-task-sketch) below makes one set of
choices for comparison. It does not settle these contracts for Ash.

| Concept | Contract to resolve |
| --- | --- |
| Task scope | Own children and their support; define normal, failed, and cancelled exit. |
| Spawn and join | Start fresh child control; define captures, result ownership, error observation, and handle lifetime. |
| Suspend and wake | Publish readiness and schedule continuation without losing completion races or duplicating execution. |
| Deadline and cancellation | Request cancellation; distinguish request, stopped operation, cleanup, and scope completion. |
| Race / first success | Choose an outcome, cancel and join losers; specify partial effects and failure reporting. |
| Bounded channel / semaphore | State capacity, full/closed behavior, wait cancellation, and fairness. |
| Yield / execution budget | Give other ready work an opportunity; state what progress assumption this requires. |
| Parallel submission | Admit only transferable captures and results under a defined sharing contract. |
| Blocking submission | Isolate foreign/blocking work and bound concurrency and queued work. |
| Runner / host entry | Explicitly acquire scheduler state; define shutdown, reentry, and foreign callbacks. |

For asynchronous handlers, distinguish a request that needs a result from a
notification queued for later execution. The first retains a suspended caller;
the second needs a destination owner, support retention, overload policy, and
failure reporting even if the publisher returns immediately. DN-0033's queued
hook sketch is one candidate: select registrations at publication, retain selected
support, and drain owned work before releasing it. Deregistration and cancellation
need separate meanings. FIFO selection does not imply FIFO completion.

Cancellation safety is operation-specific. A losing read may already have
consumed bytes; a write may have made partial progress. A first-success race does
not prove that only one external action occurred. Progress needs an owner that
survives whichever cancellation points the API admits.
[Tokio cancellation safety](https://docs.rs/tokio/latest/tokio/macro.select.html).

## Concrete local task sketch

This candidate uses one cooperative worker, lexical task groups, fresh child
control, explicit child handlers, and whole-task suspension. Cancellation is a
request observed through typed results. There is no automatic abandonment of
arbitrary task control, general continuation escape, or parallel execution.
These are comparison choices, not a proposed change to current source handlers.

### Group, task, and result ownership

Use these explanatory names; they do not introduce Ash source types or syntax:

| Name | Candidate meaning |
| --- | --- |
| `Group<G,A,E>` | One activation owns children with result `A` and error `E`, their control, pending operations, and retained reports. |
| `Task<G,A,E>` | A non-owning observation handle dependent on that group activation. Copying or dropping it changes no execution ownership. |
| `WaitResult<Q,E>` | Ordinary alternatives `Ready(Q)`, `Failed(E)`, and `Cancelled`; cancellation is part of this operation's declared result. |
| `TaskOutcome<A,E>` | Ordinary alternatives `Success(A)`, `Failure(E)`, and `Cancelled`, published only after required completion. |
| Group report | The scope body's outcome, child outcomes, and cleanup reports, with their dependencies retained and checked separately. |

Fixing the child result/error types per group avoids requiring heterogeneous
source packaging in the first comparison. Separate groups or an explicit sum
can express different child results. General result packaging remains open.
The group identity has a static scope and a fresh runtime activation, analogous
to the distinction already needed for scoped resources; a library-generated
integer alone would not enforce its lifetime.

The group owns every admitted child until completion. `try_spawn_local` reserves
the required task slot before publishing a handle and queues fresh child control.
The child starts only when the worker selects it after the caller yields. The
operation can return a declared capacity or closed-group refusal; this does not
turn every internal allocation failure into a recoverable source result.
Copying a thunk or handle does not clone a running task or its continuation.

`join` observes a stored outcome after completion. In this candidate, repeated
joins can read the same ordinary result, subject to its dependencies; one-shot
control does not require one-shot observation. A child-local resource cannot
escape through its result. A report leaving `G` cannot retain a task handle or
other dependency on `G`. Dropping an unjoined handle does not detach the child
or remove its failure from the group report.

Normal scope exit closes admission and drains existing children before releasing
group support. The comparison policy is wait-all with retained child reports.
If the body explicitly returns failure or observes cancellation, the wrapper
requests child cancellation before draining. Child failure alone is recorded;
requesting immediate sibling cancellation is a different library policy. A child
attempting to spawn into a draining group receives the declared closed result.

The following is pseudocode. The context wrapper installs ordinary handlers
inside the child; acquisition and spawn refusal are explicit branches. `cleanup`
denotes the candidate's retained invocation obligation, not a new callable API.

```text
run_local(services, () => task_scope(G, wait_all, () => {
    match try_spawn_local(G, () => {
        match acquire_input() {
            Failed(e) => Failure(e)
            Ready(input) => cleanup(() => close_input(input), () => {
                with_read_handlers(input, () => {
                    match read_next() {
                        Ready(bytes) => Success(decode(bytes))
                        Failed(e) => Failure(e)
                        Cancelled => Cancelled
                    }
                })
            })
        }
    }) {
        Started(t) => join(t)
        Refused(reason) => Failure(map_refusal(reason))
    }
}))
```

The returned group report retains the body and child outcomes and any cleanup
failures. It is not just the value selected by `join`. The example illustrates
control and ownership; it establishes no executable API, error coercion, or native
resource provider. In particular, cancellation does not mean acquisition failed
before it acquired ownership: a late successful acquisition still needs release
before the task can finish.

The input is acquired before its read handler is installed. That handler retains
the input as admitted support; `Read.next` need not carry an inner resource handle
outward in its request. The close action uses services available outside this
handler or installs its own. It cannot rely on restoring the inner read handler
after that handler has returned.
Here `close_input` returns unit and reports typed close failures through an
explicit reporting adapter; an ignored failure value would not report itself.

### One-shot suspension at the task boundary

Keep execution state separate from cancellation and completion protection:

| Axis | Candidate states |
| --- | --- |
| Scheduling | Queued, ready, running, parked, finished |
| Cancellation | No request, requested |
| Completion protection | Ordinary execution, protected cleanup or group drain |

A protected cleanup can be parked; a cancellation request can coexist with any
unfinished state. Neither fact permits deleting its control. Nested cleanup can
finish and return to ordinary body work, so protection is not synonymous with
the final phase of a task.

Each suspension creates a private wait generation with its typed reply slot and
operation registration. Parking moves the complete task configuration into the
runner's ownership: environment, ordinary frames, live source-handler captures,
clause suffixes, resource/cleanup owners, and exact interpretation. There is one
owner of executable control. The source clause does not transfer its hidden
resume capability into an ordinary library queue.

A synchronous completion returns directly without parking. For a pending wait,
registration and readiness checking close the completion race before the worker
is relinquished. Completion publishes a typed reply and makes that generation
ready at most once. Only the runner restores execution; a host callback does not
recursively run Ash control. Duplicate notifications may coalesce. A late callback
for a retired generation cannot start another execution or address reused storage.
Dropping stale notification data does not remove any duty to account for the
external operation and release its retained resources.

On restoration, the reply goes to the suspended wait expression and evaluation
continues normally. A later wait creates another generation. Thus a task may
suspend many times while every individual suspension remains one-shot.
DN-0033's bounded `park` is a different operation: its original clause may finish
and its eventual answer goes to a new consumer. This sketch retains the original
clause and its answer path.

### Handler context and work after resume

For a child, the minimal rule is explicit construction: its thunk installs the
ordinary user handlers it needs. The selected scheduling service remains at its
task root. This avoids a first-class handler-context value or automatic parent
handler inheritance in the first comparison. Captured handler closures still
need their ordinary value and resource dependencies checked. Resource providers
or foreign services also need their actual interpretation available; saving an
effect name, row, or handle alone is insufficient.

Within one task, suspension retains existing handler activations and exact
instantiation. Scheduling the task under a handler at the `join` site cannot
reinterpret its operations. Asynchronous notification handlers can use the same
model by installing a checked registration-site wrapper when constructing each
child. Arbitrary retention of an outer handler activation remains a separate
candidate with provider-state and lifetime obligations.

Consider this schematic handler clause. `Read.next` declares
`WaitResult<Bytes,ReadError>` as its result, so all three outcomes are valid inputs
to its source resumption. `wait_io` may suspend the task while that source
capability remains live.

```text
next request => {
    log_before(request)
    reply = wait_io(request)
    answer = resume reply
    log_after(request)
    answer
}
```

The execution order is: enter the clause, possibly park in `wait_io`, restore it
with one reply, resume the captured body, finish that body's required work,
return to `log_after`, then return through the remaining outer frames. A value
produced by the resumed body is not yet the task's terminal outcome. For example,
if a clause adds one after `resume`, a resumed body returning `41` must still
produce `42` after suspension. Recording `41` as task completion loses source
control. This is an extension obligation derived from the
[current resume behavior](../../spec/dynamic-semantics.md#effect-handlers-and-completion).

An existing operation returning just `Bytes` cannot receive `Cancelled` instead.
It needs an explicitly different result contract or a later admitted abandonment
mechanism. The scheduler cannot manufacture a value of the declared result type.

External support must outlive every child's use and retained result. In
`group G { resource R { spawn G child_using_R }; ... }`, `R` ends before the
group drains. The simple comparison rejects that capture. Nesting `G` inside
`R` can establish the lifetime order, but does not alone establish safe shared
access or interpretation. Proving an earlier join sufficient for a shorter
resource lifetime is a possible later refinement.

### Cancellation, operation settlement, and cleanup

In this candidate, `cancel` only records a request. A designated wait or explicit
checkpoint may observe it and return `Cancelled` through its declared result.
The task then runs ordinary source control, including `resume` and clause work,
and chooses its task outcome. A task that ignores the request can succeed. A
request received after completion does not rewrite the stored outcome. Cancellation
does not inject an exception, silently discard a suffix, or forcibly stop a worker.

For an I/O wait, distinguish the request flag from operation settlement. The
adapter attempts cancellation when supported, but keeps the registration and
buffers alive until the original completion or cancellation protocol establishes
that the operation no longer uses them. Only then does it deliver one reply.
This comparison preserves an original success or failure that wins the race;
`Cancelled` means the adapter settled the wait as cancelled. A checkpoint before
starting an operation can instead return `Cancelled` without starting it. Other
winner policies remain possible, but cannot release support prematurely or imply
rollback of external effects.

This first model retains the waiter until settlement. Returning cancellation
early while an operation continues in the group would require an explicit
transfer of its buffers and completion obligation; it is not an incidental
optimization. A foreign operation that never settles can therefore prevent
task and group completion indefinitely.

Cleanup and group draining are protected completion. During them, ordinary
cancellation delivery is deferred; a request cannot skip or restart an acquired
action or bypass joining children. The comparison permits cleanup to suspend:
the complete protected configuration and support remain owned, and the runner
continues servicing its waits while the group drains. Cancellation cannot remove
that work from the scheduler. This needs new suspension admission evidence; it
is not already established by current cleanup tests.

A cleanup operation can still return an ordinary typed failure, which the chosen
reporting adapter retains without erasing the primary outcome. Within a task,
cleanup retains structural order. Across children there is no implied total
effect order; a library may present reports in spawn order while execution
interleaves. Starting an action discharges its right to be invoked again, not
its duty to finish. Neither successful invocation nor returning a failure proves
successful native release.

For the example, a cancellation during `read_next` gives this possible order:

```text
request cancellation
    -> settle the pending read and retain its one reply
    -> resume source control with Cancelled
    -> finish source handler clause work
    -> run close_input under completion protection, possibly suspending
    -> retain task outcome and cleanup reports
    -> satisfy join and finish group draining
    -> release group-owned support
```

The position of `close_input` relative to handler clause work follows their
lexical nesting: in this example cleanup surrounds the handled call. Placing
cleanup inside the handler body would instead finish that cleanup before resume
returns to `log_after`.
Normal completion uses the existing lexical interpreter context. Cancellation
here follows normal control; it does not restore abandoned handlers to run
cleanup. Abortive cancellation would need a separate admissible-cut and closing
design consistent with current discard's surviving-context rules.

Masking cancellation does not prove termination, fairness, or deadlock freedom.
A child awaiting its own group's completion creates a join cycle. A deadline
can initiate cancellation without bounding when protected completion releases
resources. Stronger shutdown or bounded-close contracts remain separate work.

## Compiler, runtime, and library responsibilities

The distinction is between checked language mechanisms, their trusted execution
implementation, and policy expressed using them. A runtime component may be
distributed as a library, including one authored in Ash, while still depending
on compiler-recognized contracts. An ordinary interface implementation does not
establish those contracts merely by matching a method signature.

| Feature | Compiler / Core | Trusted runtime or host library | Ordinary Ash library |
| --- | --- | --- | --- |
| Group scope and task handles | Check scope identity, nonescape, support, and required group completion; validate the representation. | Retain group activation and children until completion. | Public wrapper, child inventory, shutdown policy, report presentation. |
| Spawn | Admit captures, result dependencies, and a fresh task root with its interpretation. | Create control and reserve stable task storage. | Admission limits, refusal/wait policy, queue selection, convenience functions. |
| Suspension and restoration | Validate and lower the full configuration, reply type, handlers, and owner phases. | Park and restore one control owner with unique wait generations. | Choose when to yield/wait and which ready task to select. |
| Handler context | Preserve lexical interpretation across new suspension; wider inheritance needs additional checking. | Retain admitted activations and support. | Explicit wrappers install ordinary child handlers; no first-class context feature is needed for this case. |
| Wakeups and host callbacks | Authenticate notification authority without exposing control ownership. | Close registration races; account for storage; prevent stale or double restoration and inline host reentry. | Readiness and ordering policy over opaque notifications. |
| Cancellation request and typed checkpoints | No new nonlocal control: ordinary typed data/branching plus lawful state access suffice. | Supply request storage/access and operation-specific cancellation acknowledgement. | Set/read requests, propagate them, return explicit outcomes. |
| Automatic cancellation or unwinding | Requires a new admitted cut, closing, answer, and outcome contract; absent here. | Execute any later admitted close protocol. | Choose when to request it; a token alone cannot supply it. |
| Cleanup and group drain | Extend completion validation to retained tasks and protected suspension. | Preserve unique invocation and unfinished completion; retain support while parked. | Reporting, cancellation deferral, and scheduling during drain under those laws. |
| Deadlines, join, race, task combinators | No new construct per combinator once wait/group mechanisms exist. | Clock and timer/operation registration protocols. | Timer ordering, winner policy, joining losers, error aggregation. |
| Channels, semaphores, explicit yield | No dedicated syntax needed over admitted wait/notify and storage access. | Lawful storage and wait/notify primitives. | Capacity, ordering, backpressure, fairness policy, yield calls. |
| Queues, priorities, work stealing | No queue algorithm required in the compiler; task movement needs separate parallel admission. | Storage/synchronization and safe task dispatch. | Queue algorithms, placement, batching, priorities, metrics, tuning. |
| I/O and blocking adapters | Define/check foreign entry and support boundaries; provide backend lowering as needed. | Operation settlement, buffers, callback reentry, thread affinity, native execution. | Device/file/network APIs, pool limits, platform choice, cancellation adaptation. |
| Assisted yielding or preemption | Safe-point insertion and root/control preservation; optional further work. | Save/restore safely and deliver scheduling requests. | Quantum, budget, priority policy; explicit cooperative yield is the smaller alternative. |
| Parallel tasks and shared mutation | Separate transfer/share and memory-visibility contract for transitive support. | Synchronization, storage, and foreign-thread implementation of that contract. | Pools, per-core ownership, messages, synchronization abstractions. |
| Surface syntax | Optional sugar; library calls still need checked scope/ownership rules. | No independent syntax obligation. | Functions, effect declarations, ordinary outcomes, wrappers, combinator names. |

The minimum compiler-facing extension in this comparison is checked task/group
ownership plus whole-task suspend/restore and its completion/support rules.
Typed dialect transforms can lower it without selecting a universal native stack
representation or adding a recursive Core form for every library combinator.
Native code generation must preserve those rules; the explicit evaluator could
provide a future reference execution after separate authorization. Both remain
outside current stabilization.

The minimum trusted execution boundary realizes fresh task roots, stable retained
state, wait registration/settlement, and one-owner restoration. An implementation
must account for these mechanisms even if packaged as library intrinsics. Queue
policy need not be trusted merely because it chooses schedules: where possible,
checked operations should preserve safety for every admitted ordering, with
fairness and liveness stated separately.

Ordinary library code can build the public structured-concurrency API over that
boundary. This is not a claim that today's Ash already supplies all storage,
FFI, atomics, provider authoring, or generative-scope facilities required to write
those libraries. Their own design boundaries remain in
[DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md),
[DN-0044](DN-0044-no-default-runtime.md), and
[DN-0045](DN-0045-native-compilation-and-interactive-execution.md).

As an alternative with less language work, libraries can represent computations
as explicit user-written state machines and schedule their steps. That can
express a useful cooperative protocol after suitable storage/platform facilities
exist. It does not make arbitrary current function or handler stacks suspendable,
and it does not supply new scope or foreign safety guarantees by convention.

## Scheduler behavior that affects latency and throughput

The following are candidate evaluation criteria, not current Ash requirements:

- Bound active tasks, queued work, retained bytes, I/O registrations, and blocking
  jobs. A bounded channel alone does not bound producers waiting to send or the
  total retained memory. Define admission, waiting, rejection, or coalescing.
- Separate latency-sensitive work from long CPU and blocking calls. Budget ready
  tasks as well as operations that actually suspend. An always-ready operation can
  otherwise prevent useful yielding.
- Compare explicit yields with compiler checkpoints at loop backedges and calls.
  A checkpoint's overhead and maximum delay depend on primitive operations and
  foreign code between checkpoints. Arbitrary-precision arithmetic can itself be
  substantial work. No quantum alone establishes a wall-clock bound.
- Limit uninterrupted queue draining and completion batching; periodically service
  timers and I/O. Compare locality benefits against delayed work and starvation.
- Prefer local execution where useful, but measure queue contention, migration,
  allocation, and NUMA effects. Fixed affinity and stealing have different costs.
- Keep priority policy explicit and measure starvation and priority inversion.
  More priorities do not establish deadline guarantees.
- Trace task ancestry, suspension reason, queue delay, worker use, retained
  resources, and cancellation progress. Debugging needs more than a creation stack.

Wakeup correctness is distinct from fairness. Rust's `AtomicWaker` illustrates
registration followed by a readiness check, or checking again after registration,
to close a lost-wakeup race. Wakes can coalesce; they are notifications to inspect
state, not counts of completed operations. Multiple wakes must not execute the
same task simultaneously or consume its one-shot control twice.
[AtomicWaker](https://docs.rs/futures/latest/futures/task/struct.AtomicWaker.html),
[Waker](https://doc.rust-lang.org/std/task/struct.Waker.html).

## Kernel and foreign boundary

A userspace scheduler selects ready tasks; an I/O driver supplies readiness or
completion; a timer service supplies expiry; kernel threads supply execution.
These may be packaged together while retaining different obligations. libuv is
an established example of event-loop/platform separation and worker-pool
adaptation, without providing Ash's language ownership contract.
[libuv design](https://docs.libuv.org/en/v1.x/design.html).

Pthreads or another host library could provide workers and synchronization.
Readiness backends such as epoll/kqueue and completion backends such as IOCP or
io_uring need adapters with truthful cancellation and buffer-lifetime contracts.
Backend selection should follow target and workload evidence rather than become
the public concurrency model.

In particular, cancelling an io_uring request can race with successful completion;
the cancellation request and original operation have distinct completion records.
Retained buffers and operation state cannot be freed merely because the Ash task
has requested cancellation. Late callbacks and stale operation identifiers need
an accounting protocol before storage can be reused.
[liburing cancellation](https://kernel.googlesource.com/pub/scm/linux/kernel/git/axboe/liburing/+/refs/heads/master/man/io_uring_cancelation.7).

Blocking foreign work may continue after its waiter is cancelled. Tokio cannot
abort an already-running blocking task; Go explicitly changes runtime state
around cgo calls. A future Ash boundary would need to specify ownership until
actual foreign completion, allowed callback reentry, and thread affinity.
[Tokio blocking work](https://docs.rs/tokio/latest/tokio/task/fn.spawn_blocking.html),
[Go cgo boundary](https://go.dev/src/runtime/cgocall.go).

[DN-0044](DN-0044-no-default-runtime.md) provides an exploratory reason to make
the runner selectable and omittable when unused. It does not eliminate the
storage, wakeup, cleanup, and synchronization machinery that selected tasks need,
and passive imports should not silently acquire runtime initialization semantics.

## Additional boundary for parallel execution

Task concurrency on one worker can be studied before multicore execution. A
parallel extension would additionally need rules for the entire reachable task
environment: data, closures, storage providers, resources, handlers, and hidden
control support. Moving a handle does not prove that its backing storage or
foreign resource can move. Immutable data still needs a valid sharing lifetime
and a thread-safe representation.

Possible initial restrictions include copied messages, immutable shareable data,
or explicit ownership transfer. Shared mutation would need synchronization and
memory-order rules. Spawn, join, and message delivery would need defined
visibility relationships. A `Send`-like marker name or an ordinary interface
signature alone cannot establish the required laws.

An empty outward effect row is insufficient evidence for unrestricted parallel
execution: handled state and cleanup may remain inside a computation. DN-0048's
stronger Pure Core boundary supplies a separate comparison case, still subject
to its strict evaluation and completion obligations.

## Research beyond established runtime practice

Recent scheduler research reinforces the need to keep public semantics independent
of one queue or preemption mechanism:

- **BWoS, OSDI 2023:** block-based work-stealing queues reduce owner/thief
  interference and include weak-memory verification. Its reported Tokio/Hyper
  throughput gain is much smaller than its queue microbenchmark gain. Evaluate
  whole workloads before adopting a queue algorithm.
  [Paper](https://www.usenix.org/conference/osdi23/presentation/wang-jiawei).
- **User interrupts, NSDI 2025:** experiments show more consistent low-overhead
  preemption, while identifying constraints imposed by other software layers.
  Specialized hardware does not remove runtime safety or scheduling-policy work.
  [Paper](https://www.usenix.org/conference/nsdi25/presentation/guo).
- **SBB, OSDI 2026:** combines decentralized preemption, core allocation, and
  load balancing, using task stealing for temporary skew and flow migration for
  persistent skew. It reports 1.7–5.2 times higher throughput at the same tail
  target when scaling to 48 cores in its evaluation. Its implementation uses
  user-interrupt hardware, a patched Linux kernel, and DPDK. This is evidence
  about a specialized network runtime, not a portable Ash performance forecast.
  [Paper](https://www.usenix.org/conference/osdi26/presentation/hu-kang),
  [implementation details](https://www.usenix.org/system/files/osdi26-hu-kang.pdf).

The transferable lesson is to compare preemption, core allocation, and work
distribution separately. Work stealing alone cannot solve every persistent
imbalance, and a central dispatcher can become a bottleneck. These results do
not justify putting kernel-bypass or hardware interrupts into the initial API.

## Evidence and experiments

No Ash scheduler performance measurements were made for this note. A future
experiment needs separate scope, a named question, comparison criteria, and
retention or disposal conditions. Useful comparisons would hold the public task
contract constant while varying control representation and scheduling policy.

Correctness cases would include completion before registration, concurrent
wakeups, cancellation during registration, duplicate or late callbacks, nested
handler interpretation, cancellation with running cleanup, partial external
progress, scope exit with live children, and a foreign operation that never
returns. Multicore cases would separately examine visibility, transportability,
cross-core cancellation, and concurrent access rejection.

For the concrete local sketch, compare traces through resumed bodies and the
remaining source clauses, including the `41` then `+ 1` example. Reject a child
whose supporting inner resource ends before group drain, or a result escaping
its child-local owner. Exercise cancellation before child start, after a winning
completion, during protected parked cleanup, and while a group rejects new work.
Check that repeated joins do not repeat execution, dropped handles retain group
obligations, and acquisition/cancellation races release any acquired resource.
Record which checks belong to typed admission, Core validation, runtime protocol,
and library policy. These are future comparison cases, not current test gates.

Performance comparison should report nonsuspending sequential overhead,
immediate-completion cost, suspended bytes per task, allocator traffic,
spawn/join cost, wake-to-run delay, and cancellation-to-resource-release delay.
Use mixed CPU/I/O work, skewed task sizes, bursts, overload, and several core
counts. Measure p50, p99, and p99.9 latency together with throughput at a stated
latency target and retained memory. Include offered load independent of completion
so a slowing service does not hide its own queueing delay. Record hardware,
backend, task sizes, capacity limits, and scheduling configuration.

## Open questions

The intended workloads, supported platforms, latency targets, and useful capacity
bounds remain unspecified. Those choices affect the acceptable suspension costs,
yielding policy, and foreign adapters. The task ownership, cancellation, context,
and parallel sharing questions above also remain unresolved.

The local sketch fixes a comparison baseline rather than accepting a contract.
Its main alternatives are wait-all versus immediate sibling cancellation,
explicit child handlers versus admitted borrowed context, cancellation settlement
before reply versus transfer to a group-owned operation, and suspending protected
cleanup versus a restricted non-suspending cleanup profile. Heterogeneous results,
shorter support lifetimes justified by early joins, and an abortive cancellation
cut would each need additional evidence. No answer here requires changing the
sequential stabilization target.

The initial research preference is structured, one-shot tasks with effect-based
suspension and selectable userspace scheduling. Compare selective state-machine
or CPS lowering with stackful fibers before choosing a native representation.
Treat compiler-assisted yielding and per-core ownership as further policies to
evaluate, and give parallel transfer/sharing its own semantic design. General
first-class continuations, multi-shot control, detached work, hard real-time
claims, and universal actor execution are unnecessary initial commitments.

This preference imposes no work on current sequential stabilization. A later
decision needs workload-specific latency/capacity targets and evidence that the
candidate preserves the stabilized sequential behavior while satisfying its new
ownership, completion, and scheduling contracts.
