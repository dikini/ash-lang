# DN-0056: Scoped Continuation Retention and Library Scheduling

- ID: `DN-0056`
- Status: exploring
- Related: [DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md),
  [DN-0051](DN-0051-userspace-concurrency-and-scheduling.md),
  [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md),
  [DN-0053](DN-0053-scoped-generic-cells-without-native-owners.md),
  [DN-0055](DN-0055-algebra-of-regions-lifetimes-and-ownership.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This design note is informative. It defines no current Ash semantics,
> accepts no architecture, and authorizes no product implementation. The
> bounded proof assignment below is experimental evidence. The rules below are
> candidate obligations, not an established soundness result.

## Question

Can existing resource scopes and cleanup express the lifetime and completion
gate of an executor-owned continuation store? What additional typed Core
machinery is necessary to retain and restore control, while leaving scheduling
and optional checkpoint policies in libraries?

The comparison must still express coroutines, cooperative multitasking, and
preemption at safe points. It must account for nested handlers, work after
`resume`, suspended cleanup, and a parent that waits for P while Q continues.
Kernel-thread composition must preserve local ownership with pinned workers
as its baseline. Migration is a separate ownership-transfer extension.

## Findings

- Resource ownership supplies the lifetime envelope. Cleanup can invoke a
  library drain loop before the store and its support are released. A separate
  task scope or runtime scheduling loop is not required by this derivation.
- Cleanup alone proves neither quiescence nor eventual completion. Its
  ordinary `Unit -> Unit` callback type cannot certify that the callback drained
  retained control. A finite-execution induction proves quiescence on normal
  return for the simple recursive drain below. A candidate finite analysis uses
  recursive normal-return summaries and authenticated, fresh probe facts,
  without a new gate primitive.
- Current Ash cannot put its hidden continuation capability in storage. The
  necessary semantic extension is ownership-bearing control storage, consuming
  transfer into that storage, and restoration to an admitted current consumer.
- Branch authority, external support, exact interpretation, and completion
  must be checked through these transitions. Existing analyses provide the
  basis; they do not already establish concurrent isolation.
- All three execution styles can use the same mechanism. They differ in who
  requests suspension and who chooses the next continuation. Safe-point
  preemption additionally depends on checkpoint coverage and admitted foreign
  boundaries; it is not arbitrary instruction interruption.
- Several pinned kernel-thread workers can each own a local executor and store.
  Parallelism then occurs across workers, with synchronization at admitted
  channels and host boundaries. Migration and shared-store scheduling require
  separate ownership, interpretation, and completion contracts.
- For two workers joined by a one-way FIFO, stable end-of-input links channel
  delivery to local completion. Network quiescence additionally requires both
  endpoint owners to finish and all remaining backing users to settle. Existing
  cleanup supplies release ordering; the channel protocol facts remain new.
- Bidirectional feedback needs causal completion accounting before endpoint
  shutdown. Closed root admission and discharged application obligations can
  establish stable application quiescence while passive receive loops remain
  suspended. Endpoint and backing settlement then complete network cleanup.
  Candidate protocol facts and recursive summaries check library orchestration
  against verified or admitted ledger and transport laws. The local store-state
  analysis cannot infer arbitrary accounting representation invariants. This
  derivation requires no new gate Core construct.
- A private functional ledger gives a concrete representation for registration,
  retirement, and emptiness proofs by induction. Subject to checked proof
  integration and the source driver/control obligations, its bookkeeping laws
  need no native admission. Transport and backing behavior remain external
  contracts; the derivation below is not a mechanically checked implementation.
- Untrusted proof plans and restricted induction are a candidate integration
  mechanism. The validator reconstructs claims against actual Core, checks
  transition preservation and current-state flow, and revalidates after
  transformations. No general proof search or executable proof primitive is
  required; the restricted checking rules still need a soundness argument.

These are design findings. They do not make a source library implementable
using only today's public Ash APIs.

## Context

Current [handler execution](../../spec/dynamic-semantics.md#effect-handlers-and-completion)
moves the selected continuation segment, including the selected handler, into
one clause-owned capture. Resumption restores that segment without replaying
its preceding computation. When it returns, the original clause suffix runs.
The [static rules](../../spec/static-semantics.md#effects) require exactly one
resume or checked discard on each normally completing clause path. The hidden
capability cannot enter an ordinary closure, argument, result, or queue.

Capture analysis follows latent requests through helpers and caller control.
A checkpoint helper can therefore request an effect while its caller is in a
handler clause without obtaining that clause's hidden capability. Handler
placement still determines the captured extent. A selected handler and crossed
boundaries are absent while its clause runs; a request there searches outward.

Current [resource rules](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
separate duplicable access from scope-owned release. They track dependencies
through values, closures, evidence, operation metadata, and actual calls.
Captured resource owners keep their completion obligations. Current integer
cells and native buffers do not supply an owning continuation store or a
general source-defined resource facility.

Current [cleanup](../../spec/static-semantics.md#scoped-cleanup-actions)
initializes an ordinary callback before entering its body, saves the body's
result, and invokes the callback once before returning that result. Starting
the callback consumes invocation eligibility while preserving unfinished
completion. A running cleanup can be captured and resumed but cannot be
abandoned. It may use still-enclosing resources.

[Effect Core](../../spec/elaboration.md#effect-core-lowering) already has
`Resource`, `Cleanup`, `Handler`, `Request`, and clause-scoped completion
operations. Its [independent validator](../../spec/elaboration.md#validation-boundary)
reconstructs actual dependencies and completion relationships after transforms.
Adding a library name or a matching callback type does not authenticate an
ownership contract.

The bounded inbox in [DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md#suspension-and-escape)
is the closest prior candidate: fix continuation ports, support, interpretation,
and completion at an owning destination. Its sequential proof evidence does
not establish retained execution. [DN-0051](DN-0051-userspace-concurrency-and-scheduling.md)
records broader task, wait, cancellation, and parallel execution questions.
This note tests a smaller mechanism without adopting a primitive task model.

The generic cell candidate in [DN-0053](DN-0053-scoped-generic-cells-without-native-owners.md)
stores reusable, discardable ordinary values. It explicitly excludes restricted
payload ownership. Replacing its payload type with a continuation does not
establish the transfer or completion rules required here.

## Constraints

The first fragment has one local executor, two isolated sequential computations
P and Q, and an enclosing network owner. A retention store has its own lexical
identity N. There is no simultaneous execution or worker migration.
The kernel-thread baseline composes several such local executors, with one
owning worker per store. Computations on different workers may execute in
parallel; their local stores remain exclusive and their continuations pinned.

- Start fresh computations by ordinary function calls under admitted handler
  roots. Do not clone the caller's continuation or assume a `Task` Core node.
- Give each ordinary resource authority to one concurrent process. Suspension
  does not relinquish that authority. Read-only grants and polarized endpoints
  may permit access according to their own checked contracts.
- Keep storage lifetime, access authority, completion ownership, and scheduling
  separate. Lexical visibility alone establishes none of the required sharing.
- Begin communication comparisons with one dedicated buffered channel carrying
  copied, resource-free messages. The bidirectional case adds a second channel
  in the opposite direction. Endpoints partition authority; each backing store
  has one owner. Channel ordering and readiness remain library/provider work.
- Keep every required owner and interpreter valid through the last admitted
  use and cleanup. Source results and operation operands retain existing escape
  checks; a locator must not launder a younger resource dependency.
- Begin with resumption-based completion. No queue operation implicitly cancels
  work, disposes a running cleanup, or supplies a dummy result.
- Keep scheduling, admission limits, gas accounting, readiness, and queue policy
  in libraries. No fairness, deadlock freedom, termination, latency, or performance
  guarantee follows from safe retention alone.
- Treat source sugar, macros, compiler insertion, general continuation packaging,
  and arbitrary foreign-stack suspension separately. Pinned worker composition
  needs the host and channel contracts below; continuation migration and direct
  shared-store scheduling remain separate extensions.

## Candidate directions

| Candidate | Assessment |
| --- | --- |
| Dedicated scope and runtime closing loop | Duplicates lifetime/invocation. |
| Owning resource, cleanup, checked drain | Preferred candidate. |
| Cell of functions or explicit states | Cannot retain arbitrary control. |

The preferred direction reuses the current resource and cleanup structure.
The new store kind and its ownership contract remain a semantic extension.
Whether the implementation uses a new authenticated resource payload, intrinsic
operations, or a small operation family is not selected here.

### Resource and cleanup composition

The following is schematic composition, not executable current Ash syntax.
External support surrounds the store. Cleanup's callback is created after
store acquisition and before the body; it captures ordinary store access,
never a hidden resume capability.

```text
external support {
    resource RetainedStore<N> store = empty {
        cleanup (fn () => drain(store, policy)) {
            p = run_segment(store, P)
            q = run_segment(store, Q)
            wait_for_P(store, p, q)
            R_after_P()
        }
    }
}
```

R can continue after P while Q remains retained. Only exit from the store's
enclosing lifetime requires its remaining work to complete. A library can also
wait for both computations, or let R proceed after launching both, while keeping
the same enclosing owner. Launch parent and lifetime owner are distinct roles.

On normal body return, existing cleanup saves R's result and invokes `drain`
once. The drain loops in ordinary library code. It returns only after the
store has no retained work or other required completion. Cleanup then returns
the saved result, followed by resource release. The runtime need not repeatedly
invoke a scheduler callback or choose any queue entry itself.

The library loop can have this shape, where `probe` observes the owning store,
not merely a ready queue:

```text
drain(store, policy) =
    match probe(store) {
        Quiescent => ()
        Pending => {
            advance(store, policy)
            drain(store, policy)
        }
    }
```

`advance` may select and restore ready control. A wider asynchronous library
could also wait for admitted notifications. An empty ready queue is not proof
of quiescence when blocked computations or unsettled operations still exist.
The initial ready-checkpoint fragment needs no external notification protocol.

Cleanup invokes the whole drain once; repeated `advance` calls are ordinary
calls inside that invocation. If a branch yields during drain, its fresh slot
keeps the drain pending. A running branch cleanup can do the same. Disabling
retention merely because draining has begun would break this case.

Outer abandonment requires its own proof. Existing discard can invoke an armed
cleanup in its owned closure, but the extended analysis must prove that the
store's drain and every restored computation retain their required interpreter
context. Otherwise that discard is rejected. Host failure disposal is not a
substitute for completing the drain.

### Quiescence proof for the recursive drain

Existing cleanup guarantees invocation and preservation of unfinished
completion. The recursive drain above has this partial-correctness contract:

```text
normal return of drain(N) implies Quiescent(N)
```

For the first local fragment, define W(N) as outstanding branch work: retained
captures, active restored control, and unfinished branch cleanup or close work.
`Quiescent(N)` means W(N) is empty. The store owner and the drain's own running
cleanup completion are outside W(N). Including that cleanup in the observed
work would make the condition circular: it completes only after drain returns.
A wider asynchronous contract must also account for unsettled operations.

The proof has four premises:

1. `probe(N)` reports the genuine owning store state. Its `Quiescent` result
   establishes that W(N) is empty, rather than that a ready queue is empty.
2. The executor has exclusive control. No other producer can create work
   between that observation and return. Probing occurs between `Continue`
   calls, after active restored control has returned to the driver.
3. `advance(N)` preserves ownership, authority, and completion invariants.
   Admitted control cannot bypass the recursive suffix and publish an ordinary
   return from drain. Divergence and suspension remain possible.
4. Neither return arm creates work after its established quiescence fact. In
   particular, the recursive call is followed only by its ordinary return.

Induct on the height of a finite normally returning evaluation of drain:

- In the `Quiescent` arm, the genuine observation establishes the postcondition.
  No later operation changes the work state before the arm returns.
- In the `Pending` arm, a normal return requires `advance` and then the recursive
  drain to return. The recursive evaluation is a smaller subderivation, so the
  induction hypothesis establishes `Quiescent(N)` at its return. The enclosing
  call performs no later operation that invalidates the fact.

This proves the stated implication under the premises. It requires no decreasing
work count: `advance` may resume P and cause it to yield into a fresh slot.
If this continues forever, drain never returns. The proof establishes no
termination, fairness, or eventual release guarantee.

### Composition with cleanup and resource release

On a normal path, existing cleanup invokes drain once and retains its own
completion until drain returns. The resulting order is:

```text
W(N) becomes empty
    -> drain returns
    -> the drain's cleanup completion finishes
    -> the store releases
```

The store's admission check must establish that every normal path to release
passes through this cleanup, or otherwise establishes the same quiescence
postcondition. No new runtime gate or scheduling loop is needed for this case.
Outer abandonment still needs the interpreter and completion proof described
above; normal-return partial correctness alone does not admit that path.

### Required analysis extension

The mathematical proof does not make quiescence a fact that today's checker
already knows. Current structural capability states describe available and
consumed continuation owners. Current cleanup analysis does not infer arbitrary
facts about resource contents from ordinary returned constructors.

The following candidate extends inferred completion summaries over existing
Core control. It is not an implemented analysis or a proved soundness result.
Its scope is the first local store fragment, with exclusive executor control.
The later [protocol analysis](#protocol-aware-completion-analysis) adds the
facts needed to compose those local proofs across the two-worker network.

#### Store-state and normal-return summaries

For each relevant store identity N, distinguish two states:

```text
E = W(N) is empty
W = W(N) is nonempty
```

Uncertainty is the set `{E, W}`. These states do not count work or include the
drain's own running cleanup. Identity and alias relationships come from the
resource analysis; a function or variable name does not identify an acquisition.

A function's summary, under its admitted interpretation context, is a relation
between input state, observable result case, and state at normal return:

```text
R_f subset-of InputState x ResultCase x OutputState
```

For a `Unit` drain, the result has one case. A summary establishing quiescence
permits `(E, Unit, E)` and `(W, Unit, E)`, with no output W. A missing input case
means the analysis has found no possible normal return for that input; the
summary never promises termination.

The result case is necessary for an observation. The genuine store probe has
this admitted relationship:

```text
R_probe = {
    (E, Quiescent, E),
    (W, Pending,   W)
}
```

A match on its result can establish E in the `Quiescent` arm. Ordinary
construction of that same result case does not establish the relationship.
For the minimal analysis, retain finite cases needed by the store protocol;
other result information can be conservatively merged.

#### Recursive inference

Analyse each recursive call group together, using relations for normal returns:

1. Initialize summaries for members of that group to the empty relation: no
   finite returns have yet been discovered through recursive calls.
2. Analyse each actual body using current group summaries, admitted operation
   contracts, and already checked summaries for other callees.
3. Add newly discovered possible return triples and repeat until the relations
   stop changing. For the fixed finite state and result abstractions, this is
   an ascending computation of a least fixed point.
4. Publish a completion guarantee only after convergence, when every possible
   normal output for the relevant inputs is E.

In the simple drain, the first iteration discovers the direct `(E, Unit, E)`
return. Later iterations discover returning paths through `advance` and the
recursive call. Even if `advance` may leave either E or W, each discovered
recursive return ends in E. No iteration introduces an output W.

The finite-execution induction above justifies adding returns by unfolding
recursive calls. A recursive cycle without a returning path contributes no
normal return, rather than a termination guarantee. Unknown external callees
must have conservative possible-return behavior; they cannot inherit the empty
initialization used for the recursive group being solved. A pending arm that
executes `advance; ()` introduces a possible W output and fails the check.

Relations compose through calls and sequential control. Matches retain the
correlation between an actual result case and store state. Joining control paths
unions possible returns, so an unsafe returning path cannot disappear because
another arm establishes E. Aliases and specialization must preserve the correct
store identity; unknown possible aliases require conservative invalidation.

#### Probe authentication

The probe relationship belongs to the admitted owning store provider. It must
be justified by its trusted or verified implementation, like the store's
ownership-transfer contract. An ordinary source declaration cannot assert it.

At a request, analysis authenticates the acquisition and activation relation,
sealed provider evidence, exact operation identity and arguments, and the
interpreter actually selected. An authenticated operation declaration alone
does not suffice: current source handlers retain precedence over a builtin
interpreter.

- If the genuine store interpreter is selected, apply its observation contract.
- If a source handler intercepts the request, analyse that handler's complete
  behavior. Its result type grants no automatic quiescence fact.
- A forwarding wrapper may retain the relationship if its actual control,
  including work after `resume`, establishes the same result/state summary.

The analysis therefore follows existing exact handler selection and lexical
instantiation. Generic identities may coincide after specialization; a proof
cannot assume them distinct. The authenticated contract is about the owning
store's work, not merely a same-typed counter or ready queue.

A helper making an outward probe request cannot export an unconditional
guarantee for every caller. Its summary must retain interpretation requirements
or deferred requests, checked against actual handler selection at use. If that
selection is uncertain, include all possible interpreter behavior rather than
assuming the genuine store provider. Imports preserve these conditions.

#### Observation freshness

The fact supplied by an observation is conditional and belongs to its returned
value at that point in execution:

```text
result is Quiescent implies N is E
```

Ordinary aliases and code proved to preserve N can preserve that relationship.
An operation that may change N's work state invalidates the old relationship
and any current E fact. So does a call that may change an alias of N, or loss of
the exclusive-control assumption needed for stability. Such a call must leave
both states possible unless another checked summary establishes a stronger fact.

For example, this observation cannot certify quiescence after `advance`:

```text
result = probe(store)
advance(store)
match result {
    Quiescent => ()
    Pending => ...
}
```

The value remains ordinary usable data, but its implication about the current
store state has expired. Copying the value cannot renew that implication.
A fresh probe or a verified drain can establish a new fact.

These are static provenance and validity facts. This derivation needs no
runtime epoch, source refinement type, or first-class proof token. Slot
generations for one-shot restoration remain a separate store mechanism.
Effects alone do not establish preservation; use actual inferred call and
control relationships, including handled requests and callable dependencies.

#### Actual return paths and independent validation

Compute summaries at actual normal returns, after all intervening handler and
cleanup control. A syntax walk that sees a tail call is insufficient. A handler
suffix after `resume`, or cleanup that creates new work after drain returns,
can change the enclosing expression's output state back to W or uncertainty.

For example, this enclosing expression does not inherit drain's guarantee:

```text
cleanup (fn () => create_work(store)) {
    drain(store)
}
```

The resource admission obligation is that every reachable normal predecessor
of release(N) establishes E. A verified recursive drain is one way to establish
that fact, rather than a mandatory function name or syntactic wrapper. Existing
cleanup supplies invocation and protected completion; extended analysis checks
the actual callback's postcondition and its preservation up to release.

For example, this same-typed callback fails that obligation:

```text
bad_drain(store, policy) =
    match probe(store) {
        Quiescent => ()
        Pending => {
            advance(store, policy)
            ()
        }
    }
```

Its pending arm returns without establishing quiescence. Creating work after
a successful recursive drain would likewise invalidate the postcondition.

The independent Core validator must reconstruct return summaries, probe
interpretation, and freshness from actual linked control. Imported summaries
remain authenticated to their definitions and hidden identities; they cannot
replace linked reconstruction. Callback substitution and Core transforms must
re-establish the proof, including handler and cleanup suffixes. Normal-return
quiescence does not by itself prove the separate abandonment obligations.

The extension consists of the store-state domain, result-case relationships,
freshness invalidation, recursive normal-return summaries, an authenticated
probe contract, and the check at the existing resource-release boundary.
These are new semantic analysis rules. An arbitrary `Unit` cleanup remains
insufficient, but no new gate node or runtime scheduling loop is required by
this derivation. The owning store and transfer/restore semantics themselves
remain the extensions identified elsewhere in this note.

### Candidate typed Core contract

One store activation fixes input `Unit`, answer A, resumed row rho, and required
external interpretation I. `Key<N>` is an ordinary opaque locator qualified by
the store activation and a slot generation. It carries no independent ownership.
A library answer can be `Finished | Suspended(Key<N>, Reason)`.

Let DELTA track structural capability states, sigma summarize possible captured
control, and chiN denote the store's exact resource effects. These are analysis
facts, not general source linear types or first-class continuation values.

Retention refers to the selected checkpoint clause's hidden owner c. The rule
consumes that capability by moving its capture into the store. It does not run
the retained computation, so its immediate row is the store operation's row.

```sequent
T-Retain :=
  OMEGA(N) = Store(Unit, A, rho, I)
  DELTA(c) = available[Unit, A, rho, sigma]
  current control has executor authority for N
  Admit(N, sigma)
  ===>
  GAMMA; OMEGA; DELTA |- Retain(N, c)
    ⇒ Key<N> ! {chiN}; DELTA[c := consumed]
```

`Admit(N, sigma)` checks every reachable capture represented by sigma:

1. Its owned closure includes all nested live clause captures and resource or
   cleanup owners at their structural positions. Transfer neither duplicates
   them nor moves N's own owning boundary into N.
2. Dependencies outside that closure remain protected through completion.
   Actual values, evidence, operation identities, saved results, and callable
   captures all contribute. External support can surround the store or have a
   separately proved completion order under the network owner.
3. Exact interpretation remains available at the admitted consumer. A matching
   type or effect row cannot justify replacing a missing provider or handler.
4. Branch resource authority remains compatible with all other live control,
   including suspended captures and executor code. Fresh root admission must
   check ordinary function captures too; retention alone cannot establish this.
5. Finishing the transferring clause skips no required completion outside the
   moved closure. All user handler suffixes belonging to the branch lie inside
   its suspension boundary, or have separately protected completion.
6. The answer and outward payloads obey existing escape restrictions.

Only the selected checkpoint owner becomes consumed. Nested source owners keep
their available or consumed state. Retention preparation precedes the committed
move; capacity failure cannot publish an ownerless or duplicated capture.

Restoration accepts a key and unit reply. It requires executor authority and
an actual consumer context satisfying I. Its row includes execution of the
retained computation, including future checkpoints and cleanup.

```sequent
T-Continue :=
  OMEGA(N) = Store(Unit, A, rho, I)
  GAMMA |- key : Key<N>
  current control has executor authority for N
  current consumer satisfies I
  ===>
  GAMMA; OMEGA; DELTA |- Continue(N, key, ())
    ⇒ Option<A> ! ({chiN} union rho); DELTA
```

On a live generation, the store marks the slot spent and moves its capture C
into active control. Restoration plugs C above an ordinary `Some` return
adapter and the current consumer D. Its answer goes to D, not into the finished
original checkpoint clause. A spent generation returns `None` without executing
C. Slot consumption does not mean branch completion.

The store owns the opaque control and responsibility for its completion. This
does not grant executor code ordinary access to branch resources. Private
checkpoint-handler associations with N are administrative, non-owning links;
they do not copy the store owner or grant P and Q shared mutable store authority.
Admitting those links requires the store protocol, not a general exception to
ordinary cell dependency-cycle checks.

The store's lifetime and closing contract can use existing `Resource` and
`Cleanup` structure. New validation must account for owned control in slots,
active restorations, the drain's quiescence proof, escape, and abandonment.
The derivation does not require separate `Closing`, `Drive`, or `Task` Core
constructs. It also does not establish that adding only two node variants to
today's Core would be sufficient.

### Root placement and a checkpoint helper

A private handler surrounds all branch-local source work, including handler
clauses, suffixes after `resume`, and cleanup. N and the executor's drain lie
outside that capture boundary. Its clause transfers the current capture and
returns `Suspended(key, reason)` through ordinary library control. It has no
unfinished source suffix that must survive after that return.

Checkpoint is an ordinary operation request with reply type `Unit`. The helper
below uses ordinary application, bindings, and conditional control. It returns
updated gas so a local binding does not lose the accounting update.

```text
check(policy, gas, site_cost) =
    (gas1, decision) = policy.charge(gas, site_cost)
    if decision == Yield:
        checkpoint(BudgetEmpty)
    gas1
```

Its latent row includes the exact checkpoint instance and the policy's effects.
The false path captures nothing dynamically; the static row still includes
the possible request. Restoration continues after the request, without charging
the same site again. Gas, refill, site costs, and decisions are library data and
policy. No `Gas`, `Poll`, or conditional-checkpoint Core node follows.

An outer private handler can capture a helper called from an unrelated handler
clause. A selected handler cannot handle a request from its own clause unless
another matching boundary is installed. An inner local checkpoint handler also
limits capture to its own boundary; it cannot be assumed to suspend the whole
branch. The helper never captures or invokes its caller's hidden `resume`.

### P and Q through handler and cleanup suspension

Suppose N owns slots kP and kQ. Restoring kP spends that generation and leaves
kQ unchanged. The retained P control before a source clause's `resume` includes
the clause boundary with its live nested capture. After `resume` returns, the
boundary is consumed and the completed nested control is absent. A later
checkpoint preserves whichever state actually exists; it cannot reactivate
the consumed source owner.

For a checkpoint during cleanup, the retained P segment includes the saved
result, the running cleanup completion owner, and the cleanup suffix. Starting
cleanup has already consumed invocation eligibility. Retention invokes nothing
and acknowledges no completion. The executor can run Q under its independent
authority, then restore P to execute only the remaining cleanup suffix.

If P yields while N's drain is running, P's capture stops at its private root.
The drain's own running-cleanup completion remains outside that capture. The
checkpoint clause returns to the current `Continue` consumer in the drain,
which keeps running. Capturing N or transferring that drain into its own store
would create an invalid ownership/completion dependency and must reject.

Copied channel messages become receiver-owned ordinary data. P's local
resources do not move to Q through scheduling or through those messages. The
channel implementation must supply the synchronization its endpoint protocol
requires; the owning store does not imply synchronization on every local
object. Multicore notification, visibility, and transport need separate rules.

### Execution styles

| Style | Suspension request | Selection policy |
| --- | --- | --- |
| Coroutines | Explicit yield/adapter. | Caller or coroutine library. |
| Cooperative multitasking | Library yield/wait. | Executor library. |
| Safe-point preemption | Enabled policy guard. | Executor library. |

Coroutines retain and restore direct-style control. The unit-reply fragment
can exchange copied data through channels; other reply ports require a
separately fixed homogeneous contract. Cooperative multitasking starts fresh
roots through ordinary calls and overlaps their retained lifetimes. Waiting
adapters still need readiness and settlement contracts.

For the third case, the program need not explicitly choose to yield at each
site: a producer can supply guarded checkpoints at safe points. Optionality
means that a producer or library can omit or disable them. A concrete enabled
checkpoint must pass ordinary typing and the retention admission checks.
Macro expansion and compiler insertion are separate producers of the same
typed Core; neither is a prerequisite for defining the contract.

Site legality and coverage are separate obligations. A valid checkpoint does
not prove that every loop, recursion cycle, or foreign call reaches one within
a bounded cost. Gas reaching zero only causes a yield when a check is reached.
There is no fairness or bounded-latency claim without additional coverage,
cost, scheduling, and host assumptions.

Coroutine abandonment and task cancellation are also separate. A resumption-only
store can hold a coroutine until it completes, but cannot implement arbitrary
drop-to-cancel semantics without an admitted disposal or cancellation protocol.
Session types can constrain channel progress; they do not establish network-wide
deadlock freedom in the presence of joins and other waits by themselves.

### Kernel-thread baseline: pinned workers

Kernel threads supply execution for library executors. The baseline gives each
worker exclusive control of its own store and keeps its computations on that
worker. Pinning here does not require CPU affinity. This is a candidate host
composition, not a capability implemented by current Ash.

The following tree shows ownership and placement, rather than Ash syntax:

```text
network owner
    kernel thread K1
        executor E1, store N1: P and Q
    kernel thread K2
        executor E2, store N2: U and V

polarized channels connect the workers
```

P and Q interleave on K1; U and V interleave on K2. Different workers can execute
simultaneously. The kernel chooses runnable kernel threads, while each library
executor chooses its next Ash continuation. See the host scheduling boundary
in [Linux scheduling documentation](https://man7.org/linux/man-pages/man7/sched.7.html).

Kernel preemption pauses the worker's existing execution state. It performs no
Ash capture, ownership transfer, cleanup invocation, or completion transition.
The worker later continues with the same authority. Ash safe points are needed
when detaching language control for library scheduling, rather than when the
kernel preserves the carrier thread's execution. Kernel preemption of K1 does
not select Q inside E1: P must return or suspend for E1 to choose Q.

All three execution styles remain available within each worker. Coroutine
selection, cooperative yielding, and optional gas-guarded safe-point preemption
use the same local retention contract. OS scheduling supplies the independent
outer level of preemption and parallel execution.

#### Worker entry and channel boundaries

An admitted thread entry can invoke an ordinary function to run its executor.
Admission checks the function's transitive captures, storage, handlers, provider
state, resource authority, and cleanup support. A simple initial arrangement
constructs worker-local resources on that worker and exchanges copied messages
through polarized endpoints. Shared read-only data also needs a valid lifetime
and a representation admitted for concurrent access.

Only E1 claims, retains, or restores N1's slots. Other workers publish messages
or notifications through an admitted channel; E1 processes them itself. A
notification may identify a continuation without granting its sender authority
to resume it. Sharing the host address space grants no Ash resource authority.

The channel/provider contract must establish publication and receiver visibility,
safe waiter registration, stale-notification handling, and backing protection
through the last possible access. The baseline does not require synchronization
on ordinary worker-local store operations. It does require synchronization at
these cross-thread boundaries and for any runtime representation actually shared
between workers. No concurrent memory model or channel algorithm is established
by this note.

A blocking host call occupies its worker, preventing that executor from running
its other computations until the call returns. An admitted adapter can instead
retain the waiter locally and submit fresh blocking work to another thread.
Its inputs and resource obligations remain live through actual completion;
notification returns to the owning executor for restoration. This requires its
own host-operation contract, rather than arbitrary transfer of an active Ash
or native stack.

#### Local quiescence and network completion

The recursive drain proof applies to each local store while its exclusive-control
and observation-stability premises hold. Notifications for existing pending
computations do not erase those computations' work obligations. If an external
producer can admit fresh work, a local empty observation does not establish that
the scope can release before that producer is settled.

A candidate network completion protocol must therefore:

1. Close fresh-work admission for the scope being drained.
2. Allow its existing computations to finish, including repeated retention.
3. Account for operations, notifications, and handoffs that can still create
   work or access the scope's support.
4. Drain each owned store and establish stable completion of its owned scope.
5. Release shared support only after the relevant completion acknowledgements
   and channel obligations have settled.

These are additional protocol obligations, not a general network termination
proof. The one-way FIFO and bidirectional derivations below specialize these
requirements. Closing fresh root admission must still allow existing work to
create accounted descendants until application quiescence is established.
An acknowledgement must be justified by the admitted completion protocol;
ordinary data labelled `Done` is insufficient. A transient E snapshot from each
worker cannot replace that protocol. Results must not export closed store
handles or dependency-bearing keys.

Completion of an owned Ash scope need not terminate its carrier thread. A
persistent pool can keep a worker alive after reporting scope completion. If
the network owner also owns the threads, their completion is another obligation.

### Network-wide quiescence for two pinned workers

Take one buffered FIFO channel C. Worker A owns the send polarity; worker B
owns the receive polarity; enclosing network owner R owns the channel backing.
There is no external producer or transfer of endpoint authority in this
fragment. Messages are copied, resource-free values. The chosen closing policy
processes all accepted messages; copied payloads alone do not imply that policy.

The following is a conditional normal-completion derivation using admitted
channel and worker contracts. It establishes neither a channel implementation
nor a general distributed termination algorithm.

#### In-flight message accounting

The message's passage must remain accounted for throughout these phases:

| Phase | Required accounting |
| --- | --- |
| Send preparation | A's active operation and access to C. |
| Accepted, unpublished | C's pending-publication obligation. |
| Published, queued | C's owned queue entry. |
| Receiving or copying | Receive operation and its backing access. |
| Processing incomplete | B's active or retained work, including cleanup. |

Before a send can report acceptance, the provider must account for its pending
publication and protect the copied payload. Publication moves that obligation
into queued state. Receipt cannot forget the queued work before receiver control
accounts for its processing. Backing access remains protected until copying is
complete. No transition may leave an interval in which neither side accounts
for unfinished work or access.

In the sequential receive loop below, B's existing continuation covers receipt
and handling. Separate dispatch would need to register the receiver work before
retiring the delivery obligation. The value itself remains ordinary duplicable
data; the provider's delivery and backing obligations are not duplicated by
copying it.

For the proof, let I(C) denote accepted but unpublished sends, Q(C) queued
entries, and U(C) remaining provider operations or notifications that may access
the backing. Active or suspended message handling belongs to B's local work.
These are semantic sets, not a requirement for central atomic counters. The
provider must establish their coverage and publication/visibility relationships.

#### Completing the send polarity

A's completion ordering is:

```text
finish admitted computations that can send, including cleanup
    -> drain A's local store
    -> finish_send(tx)
    -> complete A's owned scope
```

Normal return of `finish_send` establishes that no more sends can be accepted
through this polarity and that every earlier accepted send remains accounted
for. Any publication still pending belongs to C's protected provider state.
An operation retaining access to A-local memory must finish before A's scope
can complete; acceptance cannot silently leave an unprotected borrow behind.

The implementation may settle publication before `finish_send` returns or leave
an accounted publication for the provider to finish. In either case, completing
the send polarity does not release C's backing or discard queued messages.
The sealed send authority cannot reopen the same channel activation.

#### Stable end-of-input and receiver completion

B can use this ordinary recursive receive loop:

```text
receive_loop(rx) =
    match receive(rx) {
        Message(m) => {
            handle(m)
            receive_loop(rx)
        }
        End => ()
    }
```

The admitted receive contract must establish:

```text
receive(C) returns End
    implies the send polarity is sealed
        and I(C) is empty
        and all earlier queued messages have been received
```

A FIFO implementation can justify this with an ordered end marker or a final
publication watermark, provided it cannot overtake an accepted publication.
A temporarily empty queue while sending remains possible supplies no `End`
fact. An ordinary payload labelled `End` does not supply it either.

This observation is stable: the finished send authority cannot create later
input in this activation. The compiler need not prove the queue algorithm or
watermark arithmetic from an ordinary method type; those laws belong to the
admitted provider contract. Actual handler selection and result authentication
remain necessary, as for the store probe.

The receive loop returns through `End`, after preceding sequential handlers
return. That does not establish that all B-owned work is finished. Any separately
admitted work, handler suffixes, and cleanup must also complete through B's local
drain before its endpoint and scope report completion. The receiver endpoint's
closing contract must account for genuine input completion; a local empty store
alone cannot justify early receiver completion under this drain policy.

#### Joint completion condition and backing settlement

Define three distinct facts:

```text
DoneA = A's admitted work and cleanup completed
        and its send endpoint completed

DoneB = B observed genuine end-of-input
        and B's admitted work and cleanup completed
        and its receive endpoint completed

SettledC = no remaining operation or notification can access C's backing
```

A sufficient network condition is:

```text
NetworkQuiescent = no external admission remains
                   and DoneA and DoneB and SettledC
```

For this fixed network, admission can be closed by construction. A dynamic
variant must establish that phase explicitly. Stable input completion accounts
for I(C) and Q(C); endpoint and provider settlement must also account for U(C).
Queue emptiness alone cannot establish that wake registrations, callbacks, or
partially completed accesses have relinquished the backing.

A synchronous implementation may derive `SettledC` from endpoint completion.
An asynchronous implementation needs its additional settlement acknowledgement.
The fact concerns actual access, not the absence of currently runnable code.
Completion of these scopes does not require persistent carrier threads to exit.

The normal-return summaries needed by analysis include send completion, the
authenticated `End` case, each worker scope's completion, and provider settlement.
Ordinary data labelled `Done` cannot establish them. A completion notification
must follow an admitted protocol whose actual control proves its relationship
to the completed scope. Probe freshness and interpretation checks still apply.

#### Cleanup ordering and premature-release trace

The network composition can retain existing resource and cleanup structure:

```text
resource Channel<C> channel {
    cleanup (fn () => finish_network(channel, A, B)) {
        run_network_body()
    }
}
```

This is schematic composition. The library `finish_network` drives or awaits
both owned scopes and settles the channel. It must establish `NetworkQuiescent`
on normal return. The owner coordinates endpoint completion through its admitted
protocol; it does not acquire the workers' ordinary resource authority.

Existing cleanup saves the body result, invokes this finishing computation once,
and preserves its unfinished completion until return. Only afterward can the
channel resource release and the saved result return. Channel-dependent results
remain subject to ordinary escape checking. Later control cannot invalidate
the completion facts before release.

Both workers must remain able to service the channel while draining. In a
bounded FIFO, B may need to receive before A can finish sending. The closing
order must not defer B's service until after A finishes. Scheduling progress
remains a separate library and host assumption.

One possible execution exposes each premature-release hazard:

1. A's last send is accepted; C owns its pending publication.
2. A begins finishing; that publication remains protected and accounted for.
3. The message becomes queued. A can complete its send polarity while C remains
   live for delivery.
4. B receives the copy and yields during handling. Its retained continuation
   keeps receiver work unfinished even though the queue may now be empty.
5. B resumes, finishes handling, observes `End`, and drains remaining cleanup.
6. Both endpoints complete and any remaining backing users settle. R's finishing
   cleanup can then return, permitting C's release.

R may wait only for A and continue inside the enclosing channel lifetime while
B remains unfinished. It cannot complete that enclosing lifetime on A's behalf
alone. Normal-return analysis must establish the joint condition at every
channel release predecessor. No new network gate Core construct follows from
this derivation; endpoint phases, delivery coverage, and settlement are the
additional provider and completion contracts. Outer abandonment needs its own
completion and interpreter proof. Eventual completion is not established here.

### Bidirectional quiescence with causal completion accounting

Now take two buffered channels, C_AB from A to B and C_BA from B to A. Each
worker owns one send and one receive polarity; R owns both backing resources
and their enclosing lifetime. Each worker processes messages sequentially, and
handling a message may send further messages through its send endpoint. Messages
still carry copied, resource-free application data.
There is no endpoint migration or shared ordinary application resource authority.

This is a candidate normal-completion protocol. Its accounting laws must be
verified or admitted; current Ash does not already implement or check them.
An application activation below means an ordinary invocation of message-handling
code, not a new task value or Core control form.

#### Why local emptiness and end-of-input are insufficient

A locally idle A may receive work from B and send another message in response.
Two empty-queue observations can miss an accepted publication or an intervening
activation. Sealing both send polarities at that point could reject required
descendant work. Conversely, waiting for both receive loops to observe `End`
before sealing either send polarity makes shutdown circular.

The derivation therefore separates application quiescence from final worker,
endpoint, and backing completion. Application quiescence establishes that no
application work can still be generated. It does not require passive receive
loops or all provider notifications to have completed.

#### Causal coverage and resource authority

R accounts for initial application work as root obligations. Every unfinished
activation and every remaining independent producer must have a completion path
to one of those roots. Before an activation publishes a message that creates
further work, the library registers a child obligation under its existing path:

```text
register child obligation
    -> publish message
    -> receive and process message
    -> finish local processing, cleanup, and descendants
    -> acknowledge completion
```

The coverage invariant is:

> Every unfinished application computation, accepted application message, and
> remaining authority to generate application work has an outstanding completion
> path to R.

Call this invariant `Covered(R)`. It is a property to establish and preserve,
not an ordinary Boolean that the library may assert.

Registration precedes any visibility of the message and remains accounted for
through pending publication, buffering, and receiver processing. Receipt must
establish receiver responsibility before retiring transport responsibility.
Suspension preserves the processing obligation, including handler suffixes and
running cleanup. A failed send can retire its reservation only after establishing
that no accepted or deliverable message remains.

An activation's completion entry can acknowledge its parent only after its own
application code and producing cleanup have finished and all child obligations
have completed. An acknowledgement in flight leaves the parent's child entry
outstanding. The protocol matches each acknowledgement to a live entry and
retires that entry once; stale or duplicate acknowledgements cannot discharge
other work. Copied identifiers name entries but confer no accounting authority.

Completion dependencies do not transfer ordinary resource access between workers.
There remains one owner of each executable continuation and its branch authority.
A parent's outstanding dependency is not a second owner of the child's control.
Where local application code has finished, its administrative entry can remain
without retaining that code's ordinary access authority. Any support actually
used by the entry remains protected by its own enclosing owner.

The causal parent is not a lexical release owner for remote processing. A remote
dependency on A's local resource would need a separate authority and lifetime
proof; the copied-message fragment supplies none.

The completion structure need not mirror the physical communication graph.
Logical parent links can remain acyclic under R even when messages travel around
a cycle. They are administrative relationships, not resource ownership from A
to B and back to A. Each worker still mutates only its own store and accounting
records. Polarized operations convey data and completion notifications; the
proof does not require a shared atomic counter on every store operation.

#### A round trip while both workers remain available

Suppose R starts activation a on A. It sends m to B, creating b. B's processing
of m sends n back to A, creating c. The causal paths are:

```text
R -> a on A -> b on B -> c on A
```

The execution can proceed as follows:

1. R registers a before starting its ordinary invocation on A.
2. A registers b before publishing m. After a's local code and cleanup finish,
   A may return to its receive loop. Its administrative entry for a remains
   outstanding because b has not completed.
3. B receives m under b's coverage, registers c, and publishes n. B may finish
   its local processing and continue servicing its channels while c remains
   outstanding. Waiting for c must not block the entire worker's executor.
4. A receives n and processes c. This is subsequent sequential work on A, not
   simultaneous access by a and c to one ordinary resource. If c suspends, its
   continuation and authority remain owned by A's local store.
5. If c produces no more work, it finishes code and cleanup, then acknowledges
   completion. B can retire c and acknowledge b after b's own local completion.
   A can then retire b and acknowledge a to R.

The accounting entries need not retain completed application frames. A genuinely
suspended computation, such as one awaiting a reply, does retain its frames and
completion responsibility until it resumes and finishes.

A reply delivered to an already-covered continuation needs a distinct handoff
rule: establish coverage in that existing continuation before retiring delivery.
Do not make the reply sender depend on completion of the receiving ancestor's
entire activation. That would introduce an artificial completion cycle. The
existing activation remains accounted for through its later work; delivery does
not create another owner or reparent an ancestor beneath its descendant.

#### Passive service and producing cleanup

Both receive loops may still be suspended when application obligations disappear.
They remain lifetime and completion obligations, but their parked existence need
not count as application work if the library establishes that they can activate
application code only upon receiving an already-accounted message.

This restriction does not apply automatically to arbitrary blocked user code.
An independent timer, callback, producer, or retained computation that can
generate application work needs a root or descendant obligation. Worker resources
remain owned while service loops are suspended; classifying a loop as passive
does not release its authority or permit concurrent sharing.

Cleanup that can send application messages belongs to the accounted application
phase. It must finish before its producer obligation retires. Service teardown
after application quiescence must be proved unable to generate application work;
otherwise retain its producer obligation and run that cleanup before declaring
application quiescence. No running cleanup is discarded or silently skipped.

#### Two-phase shutdown and stability proof

Let G(R) be the outstanding root obligations, including independent producers.
Their descendant coverage is established by `Covered(R)`. Define:

```text
RootsClosed(R) = no further independent application work can be admitted
RootsEmpty(R) = G(R) is empty
AppQuiet(R) = Covered(R) and RootsClosed(R) and RootsEmpty(R)
```

The first phase establishes application quiescence:

1. Seal fresh root admission, including admission by R or external sources.
   This does not seal internal sends by existing accounted computations.
2. Continue servicing both workers, application channels, and completion
   notifications. Existing work may generate descendants and suspend repeatedly.
3. Establish through the authenticated protocol that G(R) is empty.

To show stability, suppose application work could appear afterward. A new root
would contradict `RootsClosed`. An existing producer, unfinished processing,
producing cleanup, or accepted message would require an outstanding root by the
coverage invariant. A passive receive loop could activate only from such an
accounted message. Each possibility contradicts `AppQuiet`. This is stronger
than combining observations taken from separate local stores.

The second phase completes service and settles backing access:

1. Seal both application send polarities. No legitimate application sender
   remains, so this cannot prevent required descendant work.
2. Let the receive loops observe genuine end-of-input and finish normally.
   Drive all remaining retained service control and non-producing cleanup.
3. Complete both workers' owned scopes and all their endpoints. Settle every
   remaining channel operation, wake registration, and completion notification.
   Private control-channel support, if separate, has the same settlement duty.
4. Return from network cleanup, permitting the enclosing backing owners to
   release and the saved body result to return.

Both directions must remain serviceable during this protocol, including with
bounded queues. Serially blocking one worker until the other completes can
prevent the messages or acknowledgements needed for completion. Scheduling and
notification delivery remain separate library and host assumptions.
Sealing application sends must not prematurely close the control support needed
to finish the protocol and establish settlement.

A sufficient final condition is:

```text
NetworkQuiescent(R) = AppQuiet(R)
                     and both owned worker scopes completed
                     and all endpoints completed
                     and all channel support settled
```

`AppQuiet` does not imply that the local stores are E: passive receive captures
may remain until the second phase. The local recursive drain proof applies at
final store completion. Application quiescence alone cannot authorize backing
release while any provider or notification can still access it.

The enclosing ordinary cleanup can implement both phases. It retains its own
unfinished completion until the finishing function returns. Resource nesting
keeps channel support live throughout; every normal release predecessor must
establish the final condition and preserve it up to release. These phases are
library protocol states, not new Core gate or task constructs.

Ownership supplies responsibility and support validity; cleanup supplies
invocation and the release boundary; the protocol supplies stable completion
evidence. This conditional derivation requires no new gate primitive. It does
not establish that today's analysis, or the local candidate analysis alone,
can validate arbitrary library implementations of the protocol. The owning
continuation store and transfer/restore extensions remain necessary.

An infinite exchange never reaches `AppQuiet`; an application deadlock may also
prevent return. Eventual completion requires additional assumptions about finite
application work, scheduling, delivery, and failure handling. Outer abandonment
and cancellation still need separate completion and interpreter proofs.

### Protocol-aware completion analysis

The smallest candidate extension adds identity-indexed protocol facts to the
normal-return summaries already derived for local stores. It checks library
orchestration against small accounting and transport contracts. It does not
infer that an arbitrary map or counter represents all unfinished work.

This is an analysis design, not an implemented checker or soundness result.
The current [control summaries](../../spec/elaboration.md#effect-core-lowering)
and [independent validation](../../spec/elaboration.md#validation-boundary)
provide the basis. They do not already establish these protocol facts or admit
general source declarations of provider laws.

#### Protocol facts and relational summaries

For the fixed two-worker fragment, distinguish these facts:

| Fact | Meaning |
| --- | --- |
| `Covered(R)` | Every application obligation has a completion path to R. |
| `RootsClosed(R)` | Independent admission is closed and earlier work covered. |
| `RootsEmpty(R)` | The actual root ledger has no outstanding obligations. |
| `Completed(x)` | An identified worker scope or endpoint completed. |
| `Settled(c)` | No operation or notification can access c's backing again. |

`RootsClosed` must account for admissions already in progress; rejecting future
calls while leaving an earlier accepted root unregistered is insufficient.
`Completed` refers to actual structural completion, or its authenticated remote
notification, rather than a user-maintained done flag. `Settled` concerns future
access as well as current inactivity. Existing local facts E(N) and W(N) remain
separate. `AppQuiet` is derived from the three network facts above, not stored
as another independently writable protocol flag.

Facts identify the actual acquisition, protocol, and runtime activation. A
same-typed counter, constructor, or different acquisition supplies no substitute.
The candidate return relation extends the earlier form:

```text
R_f subset-of ProtocolInputFacts x ResultCase x ProtocolOutputFacts
```

It is qualified by actual resource identities and interpretation requirements.
It also retains relationships such as `q identifies a live child of p in R`.
Separate Booleans saying that q and p exist cannot establish that relationship.
Aliases, projections, and calls must preserve it, or a successful admitted
lookup must establish it before use. Copying q does not copy completion authority.

Record parameters are instantiated per invocation; analysis does not enumerate
all records created at runtime. A finite summary abstraction for those parameters
and their aliases still needs a sound definition. Static acquisition identities
must not be confused with fresh runtime record keys or their reuse protection.

#### Accounting and transport operation contracts

The operation laws needed at the abstraction boundary are:

- Child registration attaches a fresh outstanding obligation to a covered
  producer before publication is possible. The parent's responsibility cannot
  disappear while that child remains unfinished. Closing direct-child admission
  is permanent for that record; later registration cannot succeed.
- Publication associates accepted work with the registered obligation. A
  reservation covers one accepted dispatch; copied keys cannot reuse it for
  another. A failed-send path can retire a reservation only after establishing
  that no accepted or deliverable message remains.
- Receipt establishes covered processing before delivery responsibility ends.
  A reply may hand off to an already-covered continuation without creating
  a completion dependency back to its own ancestor.
- A child-empty observation describes the actual children of the identified
  live record. Retirement matches a completed child and occurs once; stale or
  duplicate acknowledgements cannot discharge another obligation.
- Root admission closure accounts for earlier accepted roots and prevents new
  independent admissions in that network activation.
- Channel closure, genuine end-of-input, and settlement establish the endpoint,
  publication, notification, and backing properties used by the second phase.

These laws provide conservation of accounting and backing responsibility.
They are contracts for operations, not new Core instructions. An operation
can itself be an ordinary library function whose summary follows from smaller
operations. Native publication, visibility, callback, and backing behavior
needs a provider contract wherever its implementation is outside checked Core.

The ledger's representation laws also need proof or admission. Its empty probe
must describe the actual outstanding records, registration must retain the
required dependency, and retirement must preserve all other obligations.
Ordinary method types, integer arithmetic, or a function named `acknowledge`
cannot establish those properties.

#### Facts inferred from actual library control

Relative to those operation contracts, analysis can infer that:

1. Every publication follows registration of its matching obligation in the
   same network; receiver dispatch uses the corresponding covered record.
2. Retention preserves the link between an outstanding obligation and its
   executable continuation. Resumption finishes under the same responsibility.
3. Local completion reporting follows all required application control,
   handler suffixes, and cleanup, and acknowledgement follows checked child
   completion.
4. Application code has no unaccounted publication path through captured raw
   endpoints, closures, evidence methods, or imported helpers.
5. Passive service and finishing code introduce no independent application
   producers. Producing cleanup remains within an outstanding obligation.

These are properties of actual transitive control and authority, not effect rows
alone. A receive-loop name or callback type cannot certify passivity. External
callbacks and timers need contracts identifying their admission and completion
relationships when their behavior is not available as checked Core.

A suspension wrapper's return is not local application completion. The
`Suspended` path keeps the record outstanding together with the retained capture.
Only the path on which the application really finishes can report local
completion. A result constructor named `Finished` supplies no proof without
the inferred relationship to actual branch control. A same-typed substitution
must re-establish that relationship.

#### Closure and freshness at both levels

For an activation record p, `LocalDone(p)` means its local application control
and cleanup finished and admission of new direct children under p is closed.
A remaining producer must already have its own outstanding obligation. Under
the coverage and retirement laws:

```text
LocalDone(p) and ChildrenEmpty(p)
    permits completion acknowledgement for p
```

Before local production closes, a child-empty observation may become stale when
p sends another message. After `LocalDone`, authenticated emptiness can justify
retirement because no new direct child can be admitted. Existing children may
still produce descendants, keeping their own obligations outstanding. A local
done flag alone does not prove either actual completion or admission closure.

The same reasoning applies at the root: `RootsEmpty` becomes stable application
quiescence only with `RootsClosed` and `Covered`. Root closure must not be
assumed to preserve an earlier empty snapshot if pending admission can still
register earlier accepted work. A fresh observation or a checked preservation
summary is needed.

Ordinary aliases and proved state-preserving code may retain an observation's
result/state relationship. A relevant mutation, unknown possible alias, or call
whose preservation is unknown invalidates it. Parallel interference requires
more than a local absence of writes: the admitted transitions of the other
worker must preserve the invariant and any claimed stable fact. A transient
local E or empty queue is not stable under message arrival.

Once `AppQuiet` is established, protocol-preserving steps cannot generate new
application work: new roots are closed and every possible remaining producer
would contradict coverage and root emptiness. Acknowledgements may settle
administrative work without reopening application admission. Terminal endpoint
and backing facts likewise require contracts preventing later use.

All observations still require the actual selected interpreter and matching
network identity. An intercepted request or ordinary returned constructor does
not inherit the genuine provider's contract. Forwarding wrappers, imports,
specialization, and handler suffixes retain the earlier probe-authentication
checks. Runtime key matching and generation checks remain provider obligations;
these static facts introduce no first-class proof token or required runtime epoch.

#### Recursive application-drain summaries

The network can use this schematic library recursion:

```text
drain_application(R) =
    match probe_roots(R) {
        Empty => ()
        Pending => {
            service_network(R)
            drain_application(R)
        }
    }
```

The input facts are `Covered(R)` and `RootsClosed(R)`. The genuine `Empty`
result establishes `RootsEmpty(R)`. The service function must preserve coverage
and root closure while permitting accounted descendant work and suspension.
Each returning pending arm passes through the recursive call, and no later
handler or cleanup suffix may invalidate its postcondition.

Use the earlier least-fixed-point inference for recursive groups. Start the
group's possible-normal-return relations empty, add returns discovered from
actual bodies, and publish a guarantee only after convergence in the selected
finite abstraction. The empty arm supplies the base return with `AppQuiet`.
Returns through the pending arm inherit that fact from smaller finite returning
evaluations. Service may increase outstanding work; no decreasing count is used.

The resulting candidate summary is:

```text
Covered(R) and RootsClosed(R) at entry
    implies AppQuiet(R) on normal return of drain_application(R)
```

Unknown callees receive conservative possible-return behavior, not the empty
initialization used for the recursive group being solved. A recursive cycle
with no return establishes no progress guarantee. This inference composes
operation laws and coverage-preservation summaries; it does not prove ledger
representation laws merely by encountering recursion.

#### Composing the shutdown summary at release

A schematic finishing function keeps policy and orchestration in library Core:

```text
close_root_admission(R)
drain_application(R)
seal_application_sends(R)
finish_worker_scopes(R)
settle_channel_support(R)
```

Root closure establishes `RootsClosed` while preserving coverage. Application
drain establishes `AppQuiet` on normal return. Sealing application sends requires
that fact under the chosen process-all-accepted-work policy and must leave
required control communication usable. Worker finishing drives passive receive
loops through genuine end-of-input and completes their stores, cleanup, scopes,
and endpoints. Settlement accounts for the final operations and notifications.

The composed normal-return summary must establish `NetworkQuiescent`, including
`Completed` for each owned worker scope and endpoint and `Settled` for every
channel support owner. `AppQuiet` alone is not a summary of final local E states.
Every reachable normal predecessor of release must establish the final facts
and preserve them through intervening control. The network drain's own running
cleanup remains outside the work it must finish, as in the local proof.

Existing resource nesting and cleanup supply invocation and protected completion.
The independent validator must reconstruct protocol relationships, actual
callback summaries, interpretation, and freshness from linked Core after
transforms. Imported or source summaries do not replace this reconstruction.
Outer abandonment still requires its separate completion and interpreter proof.

#### Boundary between inference and admission

The division of responsibility is:

| Property | Inferred from library Core | Verified or admitted law |
| --- | --- | --- |
| Register/publish | Order and matching record. | Ledger coverage. |
| Completion report | Local finish and child-empty arm. | Lookup/retirement. |
| Producer coverage | Authority and actual call paths. | External admission. |
| Message handoff | Dispatch under the matching record. | Transport coverage. |
| Shutdown phases | Calls, recursion, and preservation. | Closure/settlement. |

The [minimal ledger](#minimal-library-core-ledger-and-inductive-invariant)
below supplies a paper representation proof over arbitrarily many records.
The minimal completion analyser consumes checked laws; it does not invent them
from an arbitrary map, counter, or collection traversal. Until proof integration
authenticates those laws against actual Core, their use by a checker still
requires explicit admission. Writing the paper proof does not close that gap.

Admission concerns authenticated defining operations, identities, and their
semantic relationships. It is not granted by an ordinary source declaration,
interface evidence alone, a matching type, or a callback's name. The mechanism
for admitting these laws and the sound finite abstraction for record parameters
remain design questions. Admitting a contract does not require implementing
the whole accounting algorithm or scheduling policy as a runtime primitive.

The extension is protocol facts, relational normal-return summaries, freshness
and interference checks, and validation at existing release boundaries. It adds
neither a general invariant prover nor a gate or task Core construct in this
derivation. The owning continuation store and consuming transfer/restore
semantics remain the separate required extensions identified above.

### Minimal library Core ledger and inductive invariant

Use a private functional representation to discharge the ledger-specific laws.
The following data and algorithms are schematic Core-level descriptions, not
executable source examples or a selected implementation. They give conditional
paper proofs. Mechanical authentication and the previously identified
continuation-retention extension remain separate work; this note authorizes
neither implementation nor a prototype.

#### Representation and the current state stream

Each worker keeps ordinary data with these roles:

```text
Ledger = (next: Int, records: List<Record>, pending_outputs: List<Output>)
Record = (id: Id, parent: Option<Address>, production: Phase,
          children: List<(Id, Worker)>)
Phase = Open | Closed
Id = Root | WorkId(Allocator, Int)
Address = (Worker, Id)
```

The distinguished root record lives on one worker and has no parent. R is still
the enclosing ownership scope, not an additional required thread. All other
records have a parent address. Its worker identifies the parent ledger's owner,
which need not be the allocator named in the record's identifier.

Within one network activation, each allocator has a distinct fixed label and
a private serial, initially zero. Allocation uses that serial and increments
it without reuse, including after retirement. Current
[integer operations](../../spec/dynamic-semantics.md#primitive-operations)
operate on mathematical integers, so this freshness argument needs no overflow
case. Network activations and their dedicated channels remain distinct; copied
old identifiers do not acquire authority in another activation.

Records and pending output envelopes contain ordinary metadata and copied,
resource-free payloads. Actual continuations remain in their owning stores.
An explicit child list makes emptiness structural; there is no separate cached
count to relate to that list. This is a proof baseline, not a performance result.

The worker threads ledger state through one owning event loop:

```text
drive(ledger) =
    event = next_event(...)
    successor = transition(ledger, event)
    drive(successor)
```

The driver also dispatches computation and submits pending outputs. Its proof
must establish that subsequent transitions use the successor, with reservations
and outputs installed before publication or application dispatch. No callback
may reenter an update using the previous state. Application code receives
identifiers and messages, not authority to select a ledger version for updates.

The ledger value is ordinary duplicable data, not a linear value. Privacy alone
does not prove which copy is current. The actual driver must never roll back to
an obsolete version or use it to certify current emptiness. These are source
control obligations for this loop; no generic mutable cell is required.
If an update checkpoints, its exclusive updating continuation remains retained;
another update cannot start from its old input. Kernel preemption preserves that
execution state without changing ledger ownership.

#### Collection lemmas and transition definitions

Implement lookup, insertion, update, and removal by recursion over private
finite lists. For example, removal returns whether a matching entry existed:

```text
remove(q, Nil) = (Nil, Missing)
remove(q, Cons(x, xs)) =
    if x.id == q:
        (xs, Found)
    else:
        (ys, result) = remove(q, xs)
        (Cons(x, ys), result)
```

Induction on the input list, assuming distinct identifiers, establishes:

```text
lookup returns exactly the matching entry
remove(q) returns Found exactly when q was present
ids(remove(q, xs).list) = ids(xs) minus {q}
remove(q) preserves every other entry and identifier distinctness
xs is Nil exactly when ids(xs) is empty
```

Insertion and update have the corresponding frame property: entries other than
the selected one remain unchanged. Finiteness is a representation invariant,
not a consequence of the list type alone. Current
[recursive data rules](../../spec/static-semantics.md#recursive-block-groups)
admit cyclic data. The ledger starts with finite lists and these private
functions preserve acyclicity; it accepts no arbitrary application-built list
as ledger state.

Registration updates a local parent record and queues one work envelope:

```text
register(L, p, destination, payload) =
    match lookup(p, L.records) {
        Missing => (L, Rejected)
        record with production Closed => (L, Rejected)
        record with production Open => {
            q = WorkId(this_allocator, L.next)
            successor = L with
                next incremented
                (q, destination) inserted into p.children
                Work(q, parent_address(p), payload) queued for destination
            (successor, Registered(q))
        }
    }
```

This is one pure state transformation. The driver makes the successor current
before submitting the envelope. Receipt establishes the corresponding local
record before executing its application code. The baseline permits one accepted
dispatch for each work envelope; transport redelivery would need a separate
deduplication proof and is not assumed here.

Local completion closes a record's production only after the actual application
control, handler suffixes, and cleanup finish. A suspension wrapper returning
does not qualify. Root closure instead closes fresh independent admission after
earlier admissions and remaining producer authorities have been accounted for.

Local retirement is:

```text
retire(L, p) =
    match lookup(p, L.records) {
        non-root record with production Closed and children Nil =>
            remove p and queue Ack(record.parent, p)
        otherwise => L
    }
```

Acknowledgement processing finds the named parent and removes the child whose
identifier and destination match that completion envelope. Unknown parents,
unknown children, and redundant acknowledgements leave the ledger unchanged.
The destination match uses the sending peer established by the polarized
endpoint. The root record remains available for observation.

These functions are private protocol implementation. Application payloads cannot
be injected as completion envelopes, and application code cannot bypass the
driver to close arbitrary records or publish through raw control endpoints.
Those authority and emission properties need proof from the actual Core.

#### Local and network inductive invariants

The local representation invariant states:

1. Record and child lists are finite, acyclic, and have distinct identifiers.
2. Each allocator's serial is beyond every serial it has issued; none is reused.
3. A record's parent and each child's destination remain fixed.
4. Closed production cannot reopen or accept another direct child.
5. The single current state stream accounts for pending outputs before they
   become visible, and submission does not replay an already accepted output.

The network invariant additionally relates all workers' ledgers, pending
outputs, native transport state, and active or retained application control:

1. Every unfinished application computation has its corresponding outstanding
   record and completion path to the root, including through suspension.
2. Every pending or accepted work envelope has an outstanding parent dependency;
   receiver dispatch continues responsibility for that same obligation.
3. Each logical non-root obligation has one parent, and every live non-root
   record is connected to the root through outstanding dependencies. There is
   at most one executing or retained owner of its application control.
   Registration introduces a fresh child beneath an existing record, so these
   logical paths have no cycles.
4. A closed application record has finished its own control and cleanup and
   cannot admit another direct child. Any remaining producer has a separately
   registered obligation.
5. A completion acknowledgement originates only from retirement of a closed,
   childless record. Its parent dependency stays outstanding until the matching
   acknowledgement is processed.

Completed records awaiting acknowledgement can be represented by their parent
dependency and pending or in-flight acknowledgement rather than a live local
record. Already processed duplicate acknowledgements are harmless redundant
control traffic. The invariant does not require that traffic to keep a completed
application obligation live, but its backing access still needs settlement.

These logical edges are administrative dependencies, not duplicated executable
ownership or permission for one worker to access another's ordinary resources.
The network invariant includes source control properties: the pure function
that writes `Closed` cannot itself prove the caller's computation finished.

Initially, only the open root record exists. Its child list, the other workers'
record lists, and all pending-output lists are empty. It represents fresh
admission authority; no application branch or work envelope has started. This
establishes the base case. Each legal transition must preserve the local and
network invariants under the native contracts stated below.

#### Registration preservation proof

For a missing or closed parent, registration returns the unchanged ledger.
For an open parent p, allocator freshness gives a child q that has never been
issued. The insertion and update lemmas preserve identifier distinctness and
all unrelated entries. Incrementing the serial preserves freshness.

The new dependency p to q and q's pending work envelope appear together in
the successor. Since p already has a path to the root, q acquires one before
publication or execution. No previous obligation disappears. Because q is new,
adding that edge cannot create a cycle. A proof may order births by transition
history; no shared runtime birth counter is needed.

The driver and transport handoff then preserve coverage from pending output
through accepted publication and receiver processing. The receiver establishes
its record before dispatch. This proves registration preservation relative to
the current-state, dispatch, and native handoff premises, rather than from the
insertion lemma alone.

#### Retirement and acknowledgement preservation proof

Retirement has two distinct stages:

1. Local retirement checks `Closed` and `children Nil`. The control invariant
   establishes that the record's own application code and cleanup finished.
   Child-list emptiness and the network invariant establish that no descendant
   application obligation remains. Closed admission prevents new direct
   children. Remove the record and queue its acknowledgement in the successor;
   the parent dependency remains outstanding during this handoff.
2. Matching acknowledgement processing removes that parent dependency. Source
   emission proves that the acknowledged subtree finished, and faithful transport
   relates the received envelope to that emission. The removal lemma preserves
   all other children and records. The logical tree loses only a completed leaf.

After local removal, repeating retirement finds no record. After dependency
removal, repeating the acknowledgement finds no matching child. Neither action
can discharge unrelated work, and non-reuse prevents a late acknowledgement
from matching a newly allocated child with the same identifier.

The source protocol proves the relationship between acknowledgement and actual
completion; transport need only preserve the submitted envelope and origin.
No separate native law saying that an arbitrary `Ack` means completion is needed.
If source code can forge that envelope or close a live computation's record,
the network invariant fails even though the list operations remain correct.

#### Emptiness and stable application-quiescence proof

The root probe is a pure lookup and pattern match over the current state:

```text
probe_root(L) =
    match root_record(L) {
        production Closed and children Nil => Quiet
        otherwise => Pending
    }
```

The collection lemma establishes that `children Nil` means no outstanding root
dependencies. By the network invariant, every unfinished application computation
or work envelope requires such a dependency. None therefore remains. Root
closure prevents new independent work, and there is no remaining covered
producer that could create descendant work. This establishes stable `AppQuiet`.

An open root with no children cannot report `Quiet`. An old ledger snapshot
cannot certify current emptiness; the driver and freshness proof must establish
the argument's relationship to current state. The observation law comes from
this actual pure function and its invariant, not a native emptiness probe or
an ordinary constructor named `Quiet`.

Passive receive loops and remaining notifications may still exist. Empty
pending outputs do not prove that accepted publications or native backing users
have settled. The second shutdown phase must still finish worker scopes and
endpoints and establish `Settled` before the enclosing cleanup can return.

#### Proof integration and remaining native contracts

The paper argument gives concrete lemmas to validate, not an automatic capability
of the candidate finite completion analysis. Checked use must authenticate:

1. Collection and freshness lemmas against their actual Core definitions.
2. Initialization and transition preservation of the representation invariant.
3. The driver's current-state flow, publication ordering, and absence of stale
   reentrant updates.
4. The correspondence between record closure and actual branch completion,
   retained control, cleanup, dispatch, and private acknowledgement emission.
5. Composition of those results into the protocol and release summaries, with
   reconstruction after imports, specialization, and Core transformations.

Ordinary privacy, callback types, or source assertions cannot supply those
proofs. The [restricted integration mechanism](#restricted-proof-integration-at-the-core-validation-boundary)
below is a candidate for checking them against Core. Its exact rule set and
soundness remain open; the paper proof cannot yet replace admission in a
checked program. A transform that changes removal, dispatch, or state flow
must re-establish the affected lemmas and completion facts.

With that integration, ledger-specific admission can be removed. The remaining
external contracts concern:

- Faithful submission and delivery: native transport does not invent or alter
  protocol envelopes and delivers each accepted work envelope at most once.
  Source dispatch preserves that uniqueness. Application data cannot impersonate
  protocol origin.
- Acceptance and failure: a definitely unaccepted submission has no deliverable
  message; acceptance transfers publication responsibility to protected native
  state. An uncertain outcome remains outstanding and cannot be blindly retried
  or retired as unaccepted.
- Publication, receipt, and readiness: copies become visible with a continuous
  handoff of delivery responsibility; waiter registration and notifications do
  not lose required work or retain unprotected access.
- Native closure and settlement: genuine end-of-input follows accepted work,
  and completed endpoints plus settlement account for every possible future
  callback, wake, or backing access before release.

Eventual delivery and scheduling progress are additional liveness assumptions,
not consequences of the ledger proof. Internal failure still supplies no source
cleanup guarantee. The previously required owning continuation store and its
transfer/restore semantics remain foundational obligations. Removing admission
of bookkeeping laws does not remove those extensions or make application
quiescence sufficient for final resource release.

### Restricted proof integration at the Core validation boundary

The candidate mechanism checks restricted inductive summaries using untrusted
proof plans. It reconstructs a derivation against the actual Core body, rather
than searching for arbitrary invariants or accepting an earlier permission.
It is intended for the finite-list ledger above, not arbitrary representations
or all behavior-preserving transformations.

This would extend the current
[independent validator](../../spec/elaboration.md#validation-boundary) and the
boundary accepted in [AD-0007](../decisions/AD-0007-typed-core-dialects.md).
It adds verification rules and metadata, not executable Core operations or
source proof values. No checker, proof certificate, or soundness result is
implemented by this note.

#### Untrusted proof plans and claim binding

A helper can carry metadata with these schematic roles:

```text
target:       actual Core function binder
claim:        RemoveById for these types and key projection
induction:    list argument xs
dependencies: verified key equality
```

`RemoveById` selects a restricted claim schema: membership and result-case
relationships, preservation of whole retained entries, and identifier
uniqueness. Its [precise contract](#removebyid-claim-and-checking-rules)
preserves their order and contents, including parent, phase, and children
fields. The plan nominates what to check; it grants none of those facts.

Validation binds the claim to actual function and nominal identities, argument
positions, projections, instantiations, and the current body. A matching type,
function name, source origin, or copied node identifier is insufficient.
Schema preconditions must be established at every use that relies on its
postcondition. An ordinary source assertion cannot discharge them.

The metadata can remain outside executable Core and is not passed to functions
at runtime. How a library or frontend supplies plans is separate from this
typed Core contract; no source syntax is selected here.

#### Restricted vocabulary and structural induction

For the initial ledger, the checker needs facts about finite lists, membership,
absence, uniqueness, preservation of unrelated entries, fixed record fields,
counter freshness, current state, production closure, and actual completion.
These predicates have defined meanings. A function returning `true` cannot
introduce `Unique`, `Current`, or `Covered`.

Constructor equations include:

```text
Finite(Nil)
Finite(Cons(x, xs)) exactly when Finite(xs)
Unique(Cons(x, xs)) exactly when Unique(xs) and x.id is absent from xs
```

The checker follows actual Core matches, equality branches, substitutions,
constructor reconstruction, and calls to verified helpers. Identifier equality
must use actual integer/constructor semantics or a checked equality helper;
an arbitrary Boolean-returning method supplies no equality fact.

Representation lemmas initially admit only ordinary data computation and
certified pure callees. An empty outward effect row does not establish that
fragment: handled requests still introduce control behavior. Unsupported
effectful helper bodies cannot silently inherit pure collection lemmas.

A recursive postcondition is available as an induction hypothesis only for a
call on a checked proper constructor subterm of the finite induction argument.
The call's actual arguments must match the hypothesis's instantiation. The
whole input cannot assume its own postcondition. Finiteness comes from the
private representation invariant, not from the ordinary data type alone.

Ordinary lemma dependencies can form an acyclic graph. The first fragment
need not support arbitrary mutually recursive induction. This is distinct
from the earlier fixed-point analysis of possibly nonterminating drain loops.

Fresh allocation needs only the checked counter pattern:

```text
allocated_id = WorkId(owner, next)
successor.next = next + 1
```

Initialization and current-state preservation establish that the counter does
not reset or reuse an earlier value. Together with mathematical integer
semantics, this proves non-reuse without a general arithmetic solver or a
stored history of retired identifiers. More complicated arithmetic need not
be accepted by the initial proof fragment.

#### RemoveById claim and checking rules

Bind the claim to actual Core function f, its list and status constructors,
and its key projection. Let `UniqueKeys` name the earlier uniqueness predicate
specialized to those projected keys. The contract is:

```text
Precondition:
    Finite(xs)
    UniqueKeys(xs)

Normal-return postcondition for f(q, xs) = (ys, status):
    ys = erase(q, xs)
    status is Found exactly when q occurs among the input keys
    status is Missing exactly when q is absent from the input keys
    Finite(ys)
    UniqueKeys(ys)
```

Define the expected sequence mathematically:

```text
erase(q, Nil) = Nil
erase(q, Cons(x, xs)) =
    if key(x) == q:
        xs
    else:
        Cons(x, erase(q, xs))
```

This is a logical definition of the claim, not an executable helper or a new
Core primitive. Input uniqueness makes removal of the matching head removal
of the only matching entry. Sequence equality permits different list-node
allocations but preserves the same retained entries in the same order. Merely
preserving their identifier set would allow a retained record's phase or parent
to change. The checker can track original entry binders to establish preservation
without deciding equality of arbitrary payloads.

The initial rule families are:

| Rule family | Established relationship |
| --- | --- |
| Constructor cases | Actual Nil/Cons cases and bound components. |
| Predicate unfolding | Finiteness, uniqueness, membership, and absence. |
| Key equality | Equality or inequality from a verified comparison. |
| Tail induction | The claim for a checked smaller input. |
| Result reconstruction | Actual entries, sequence order, and result tag. |
| Checked helper calls | Verified claims with established preconditions. |

Each reachable branch must satisfy the contract. A proof plan cannot omit a
difficult arm. Facts refer to actual binders and constructor identities, not
their source spellings. An induction call must target the function being
checked, pass an actual constructor tail of the finite induction input,
establish its preconditions, and instantiate the remaining arguments correctly.

A tail binding alone does not establish well-founded descent: for cyclic data,
the tail can lead back to the whole input. The `Finite` premise excludes that
case. Calls on the unchanged input, unverified callees, and circular ordinary
lemma dependencies cannot assume the claim being checked.

#### Reconstructing the removal lemma

The validator checks three cases of the actual `remove` body. Let tail denote
the actual pattern-bound tail, independently of its binder's source name.

1. **Empty input.** `Nil` contains no requested entry. The returned `Nil` and
   `Missing` establish the sequence, status, finiteness, and uniqueness clauses.
2. **Matching head.** Verified comparison establishes `key(x) = q`. Input
   uniqueness establishes q's absence from tail. Returning tail therefore
   removes exactly the requested entry, preserves every other entry, and
   correctly reports `Found`.
3. **Nonmatching head.** Verified comparison establishes `key(x) != q`.
   Constructor decomposition supplies `Finite(tail)`, `UniqueKeys(tail)`, and
   absence of `key(x)` from tail. The actual call on tail may use the induction
   hypothesis. Its returned ys is `erase(q, tail)` and introduces no new entry,
   so `key(x)` remains absent from ys. The actual result `Cons(x, ys)` preserves
   the original head and sequence order, retains uniqueness, and has the required
   status: membership of q in the original input equals membership in tail.

The reconstruction checks returned values, not just that a suitable constructor
appears somewhere in the body. Replacing a retained entry with a same-key entry
whose phase changed fails whole-entry preservation. Returning the wrong status
fails the result/membership relationship even if the list itself is correct.

#### RemoveById soundness obligation

The required checker theorem is:

> If the checker accepts `RemoveById` for the actual linked Core definition of
> f, every normally returning execution of f(q, xs), from a well-formed runtime
> input with a finite list and unique keys, satisfies the stated postcondition.

The argument must establish local rule soundness under Core evaluation and
justify recursive-hypothesis use by induction on the finite input list.
Symbolic constructor and branch facts must describe the actual
[matching semantics](../../spec/dynamic-semantics.md#tuples-constructors-and-matches),
including nominal identities and the actual selected branch. All callee claims
and key-comparison facts used by the derivation need their own checked basis.
This is a normal-return guarantee, not a network termination or scheduling
guarantee. The theorem is a proof obligation, not an established result.

The following changes must invalidate the affected derivation:

| Changed body | Missing justification |
| --- | --- |
| Nonmatching result becomes Nil | Unrelated-entry preservation. |
| Retained record changes phase | Whole-entry preservation. |
| Every result reports Found | Membership/result correlation. |
| Recursive call uses whole input | Proper-subterm induction. |
| Comparison is arbitrary Boolean code | Verified equality semantics. |

A valid alternative algorithm may also fall outside the initial rule fragment.
It needs another checkable derivation; recognizing arbitrary equivalence is
not required. The theorem binds to the current linked definition, so any Core
transformation must reconstruct the derivation before reusing its summary.
Only a complete, budgeted check may publish the claim.

The checked summary remains a data-operation fact. `Found` establishes that the
child existed in the input list; it does not establish that the child finished.
An empty resulting child list still needs current-state provenance and closed
production before acknowledgement is permitted. The proof chain is:

```text
checked removal definition
    -> exact data-preservation summary
    -> ledger transition preservation
    -> completion and current-state checks
    -> shutdown and release justification
```

This identifies a first concrete claim and rule-soundness obligation for the
restricted checker. It supplies no implementation or mechanically checked proof.

#### Transition preservation and protocol composition

Collection lemmas establish data-operation meaning. A restricted preservation
check then relates actual ledger updates to permitted protocol transitions.
For registration it reconstructs:

```text
check the parent is open
    -> construct a fresh child identifier
    -> insert the matching dependency
    -> queue the matching work envelope
    -> return the successor state
```

The relationships use actual values and fields. Naming an expression
`registration` supplies no evidence. Under the defined ledger invariant,
adding a fresh child beneath a covered parent preserves rooted coverage.

The retirement check requires actual local completion, closed child admission,
and actual child-list emptiness before record removal and acknowledgement
enqueueing. Matching acknowledgement processing uses the verified removal
lemma and the peer established by the polarized endpoint. Source emission and
faithful transport establish its relationship to the completed subtree.

This is a restricted simulation check: Core transitions must implement the
permitted steps of the ledger model. Checked initialization supplies the base
case; transition preservation establishes the invariant for every finite
execution prefix, including interleaved worker steps under the admitted native
contracts. `Covered` is not an uninterpreted assertion attached to a callback.

The model's preservation rules become part of the validator's trusted logic
and need a soundness argument. They are verification rules, not generated
runtime events. Library code still chooses scheduling, service order, and
shutdown policy within those checked relationships.

#### Current-state tracking and actual completion

Collection induction does not prove that a caller uses the current ledger.
Track a fact with this schematic meaning:

```text
Current(R, L)
```

A verified transition returning L1 establishes the successor relationship.
Subsequent updates and observations must use that successor or a value proved
equivalent to it. This call pattern therefore fails when the transition may
change authoritative state:

```text
L1 = transition(L, event)
drive(L)
```

Copies of L remain ordinary data. They do not retain a permission to update or
certify the current ledger after that relationship expires. On a branch proved
to leave state unchanged, the analysis can preserve the corresponding equality.
This adds neither a source linear type nor a runtime version counter.

Actual completion is a separate control fact. Writing `Closed`, returning
`Finished`, or giving a callback the right type cannot establish it. Analysis
must reconstruct the relationship to branch control, handler suffixes, retained
continuations, and cleanup. A suspension wrapper's `Suspended` return keeps its
obligation outstanding. Captures, resumptions, and callback calls must preserve
the state and completion relationships they actually carry.

The normal-return analysis then composes verified transitions into recursive
drain and shutdown summaries. All relevant transitive calls and interpreted
requests need checked preservation or conservative treatment; an unknown
callee cannot inherit a protocol guarantee merely from its outward row.
Structural list induction does not replace this control analysis.

#### Independent revalidation after transformations

Ordinary Core validation checks types, scope, identities, and control first.
The candidate proof pass checks helper claims against those actual bodies,
reconstructs initialization and transition preservation together with the
required control relationships, and supplies only checked facts to completion
summaries and release checks. It must run again at each validation boundary
after transformation.

The transform obligations are:

| Change | Required treatment |
| --- | --- |
| Renaming or supported simplification | Replay the derivation on changed Core. |
| Inlining or specialization | Instantiate or regenerate a checked derivation. |
| Algorithm or representation replacement | Establish the replacement's lemmas. |

Normalization can be bounded and limited to supported forms. The checker need
not recognize every equivalent program. A valid optimization can produce Core
outside the proof fragment; the compiler must preserve a checkable form or
produce a supported derivation. It cannot retain an old permission based only
on the transform's equivalence claim.

Imports likewise need their actual linked definitions and checkable derivations
at this boundary. An interface claim alone supplies no representation proof.
Binding a plan to an old body by name, origin, or identifier cannot authenticate
the current body. If a needed release fact cannot be reconstructed, validation
fails before execution; no stale permission authorizes release.

#### Bounded checking and remaining soundness work

The candidate adds restricted claim schemas, structural-induction checking,
ledger-transition preservation checks, and current-state/completion composition.
It adds no general invariant discovery or unbounded proof search. Attempts,
instantiations, traversals, and retained facts must charge the existing
cumulative validator resource budget. Exhaustion yields no partially checked
claim or release permission; there is no separate unlimited proof allowance.

The rules still need a soundness argument relating accepted derivations to
actual Core evaluation and protocol steps. The exact supported schemas,
normalization limits, proof-plan representation, and treatment of unsupported
transforms remain open. This note proposes the checking boundary rather than
claiming to have implemented or proved it.

With sound rules and successful revalidation, ledger registration, retirement,
and emptiness can rely on checked source definitions. The native transport and
backing premises above remain external contracts, and continuation retention
still needs its previously identified semantic extension. There is no new task,
gate, proof value, or executable Core primitive in this derivation.

### Migration as a separate ownership-transfer extension

Pinned workers already provide parallel execution. Moving a suspended computation
to another worker requires a separately admitted handoff of unique execution
authority and completion responsibility. It is not enabled by sending an
ordinary copied `Key<N1>` to K2.

The migration contract must check the entire owned capture forest, including
environments, nested captures, provider state, storage, saved results, and
cleanup. External support must remain valid and required exact interpretation
must be available at the destination. Thread-affine resources and native or
cleanup requirements can prevent a move. Publication must establish receiver
visibility and one consumer of the handed-off authority.

The contract must also say whether N remains the logical owner during a checked
execution handoff or work is rehomed into another store. Rehoming requires
rechecking fixed input/answer ports, administrative store associations, and the
completion return path. In particular, `Key<N1>` cannot become `Key<N2>` by
copying or changing a label. This note derives no such rehoming operation.

Work stealing can later choose among admitted transferable computations. It
does not establish their transferability. Moving a whole executor domain would
likewise require a contract for all of its owned control and support.

Direct concurrent access to one store by several workers is another extension.
It would need synchronized claims and a concurrent observation/closing protocol;
atomic slot claims alone do not preserve the single-owner quiescence proof.
Neither migration nor shared-store scheduling is required by the baseline.

### Erlang comparison

Erlang provides an execution-model comparison: lightweight processes execute on
multiple scheduler threads, and processes communicate by asynchronous signals.
See its [scheduler-thread overview](https://www.erlang.org/doc/system/eff_guide_processes.html#smp-run-time-system)
and [process communication rules](https://www.erlang.org/doc/system/ref_man_processes.html).
The following correspondences are design analogies, not Ash implementation or
performance claims:

| Erlang concept | Proposed Ash counterpart |
| --- | --- |
| Lightweight process | Computation with owned control and resource authority. |
| Scheduler thread | Library executor on a kernel-thread worker. |
| Reduction budget | Library gas policy evaluated at checkpoints. |
| Message communication | Polarized channels. |
| Runnable process queue | Library queue of continuation keys. |

Erlang uses reduction allowances before scheduling a process out; its
[runtime flags](https://www.erlang.org/doc/apps/erts/erl_cmd.html) describe that
budgeting. The Ash proposal makes checkpoint accounting and scheduling policy
library-defined and optional, subject to site legality and coverage. The
analogy does not equate a reduction with a particular Ash cost unit.

Erlang's scheduler implementation includes process migration and work stealing
between run queues, as described in its
[process-management documentation](https://www.erlang.org/doc/apps/erts/processmanagementoptimizations.html).
Our pinned-worker baseline deliberately leaves that behavior to the separate
ownership-transfer extension above. Erlang is evidence that scheduler-local
queues and migration can coexist, not proof of Ash's transfer contract.

Erlang also provides links, monitors, and supervision for process relationships
and failure handling; see its
[process relationship rules](https://www.erlang.org/doc/system/ref_man_processes.html#links).
Those mechanisms address different obligations from the proposed lexical
resource ownership, retained running cleanup, and checked completion of Ash
scopes. No supervision or termination policy is adopted by this comparison.

### Boundary of the required extension

| Concern | Reused machinery/library | Additional obligation |
| --- | --- | --- |
| Lifetime | Resource scope. | Admit owned-control payloads. |
| Completion | Cleanup and library drain. | Prove quiescence on return. |
| Retention | Exact capture. | Consuming transfer to the store. |
| Restoration | Ordered restore. | One claim, current consumer. |
| Authority | Dependency/completion analysis. | Check branch isolation. |
| Checkpoints | Calls, data, matches, requests. | Admit supplied sites. |
| Scheduling | Queues, recursion, joins. | Wider wait/notify contracts. |
| Representation | Explicit control. | Stable slots and checked generations. |
| Pinned workers | Local executors/stores. | Thread entry and channels. |
| Network finish | Cleanup and channels. | Causal coverage and settlement. |
| Migration | Separately admitted handoff. | Whole-capture transfer checks. |

Storage must also account for capacity before committing transfers, preserve
failure ownership, and survive lowering. No native continuation representation
is selected. The completion and authority obligations apply after transformations
and during abandonment as well as on the ordinary return path.

## Evidence and experiments

### C1 bounded ownership and completion proof assignment

[C1 #71](https://github.com/dikini/ash-lang/issues/71) asks whether the local
store transitions can preserve one owner and its completion obligations. This
assignment authorizes a finite Lean model, not an evaluator implementation.
[CP-0026](../proposals/CP-0026-scoped-owned-continuation-storage.md) is the
proposed contract to compare with that model; its acceptance is separate. The
[active task](../tasks/TASK-0057-local-retained-control.md) records the proof
and the remaining product gates.

Model a single store activation, finite branches and slots, and one executor.
Include an active selected-clause capture, nested live and consumed owners,
owned resource and cleanup completion, external support, exact consumer
interpretation, slot generations, reserve refusal, committed transfer, restore,
normal branch return and failure disposal. The model must represent the
current consumer separately from the clause that transferred a capture. It
must state how the store's owning boundary and outside completion relate to
each capture, rather than assuming a successor is safe.

Compare successful paths with self-capture, skipped outside completion,
duplicate/stale keys, incompatible interpretation, branch-local dependency
escape, and preparation failure. Check both armed and already-running cleanup
and a second yield during drain. Show the actual premise that excludes each unsafe
path. Include a finite trace where restored control returns to its current
consumer, and an unrelated live slot remains unchanged. For this sequential
fragment, compare shared access to a still-live outer cell with a branch-local
owner; one scope/completion owner persists in each case. The earlier concurrent
process isolation constraint remains future parallel pressure, not an added
local disjoint-footprint requirement.

Prove preservation of the selected ownership and completion invariants for
each admitted transition and finite traces, no second restoration of the same
generation, and no release with unfinished owned work. Preparation refusal
must leave the original owner intact; post-commit teardown must distinguish
successful disposal from reported incomplete teardown without double release
or a claim that source cleanup ran. Prove these from local step
premises, not by taking the successor invariant as a premise. State any
provider, scheduler, runtime or admission assumptions explicitly. A separate
proof of C3's recursive normal-return analysis is required before its release
facts are used; this assignment does not prove it.

Retain the model and a correspondence map only if the named examples and
proof obligations are independently reviewed and pass the frozen scoped
[AD-0012](../decisions/AD-0012-proof-development-feedback-and-build-reuse.md)
integration gate. Otherwise retain the finding in this note and discard the
prototype; revise the proposed contract if the comparison exposes a semantic
gap. Neither outcome establishes compiler or runtime correctness, external
provider laws, termination, or the wider network claims in this note.

This note contains a paper derivation against the linked current specification.
It includes the partial-correctness argument above under explicit premises,
but supplies no executable retention implementation, machine-checked proof,
benchmark, or new current-language example. Existing one-shot, cleanup, and
resource evidence transfers only to the sequential invariants it actually tests.

The bidirectional accounting comparison draws on Dijkstra and Scholten's
[termination detection for diffusing computations](https://www.cs.utexas.edu/~EWD/transcriptions/EWD06xx/EWD687a.html).
Their signalling scheme accounts for delegated work across a network that may
contain cycles, while maintaining a rooted completion relationship. This is
conceptual evidence for separating physical communication from completion
dependencies. It is not a transferred proof of Ash's retained continuations,
resource authority, cleanup, passivity restrictions, or provider contracts.

The next comparison should exercise the same control under coroutine selection,
cooperative queue selection, and guarded gas selection. It should use an
owning resource plus existing cleanup as the baseline against a dedicated
runtime closing loop. Compare semantic obligations and required Core/runtime
changes before comparing performance.

Required positive cases include:

- R waits for P, continues with Q retained, and exits only after the enclosing
  drain completes Q.
- P checkpoints before and after an inner clause's `resume`, preserving the
  appropriate nested owner state and returning to the current consumer.
- P checkpoints in cleanup, Q runs, and P completes the remaining cleanup once.
- P checkpoints again during store drain; the outer drain remains protected.
- A false gas guard performs no request, while the true guard preserves its
  committed accounting update through restoration.
- Copied keys can be stale without restoring control twice; lost ready-queue
  entries cannot make the owning store appear quiescent.
- Drain returns after finitely many repeated yields only through a final
  genuine quiescence observation; no decreasing work count is assumed.
- Mutually recursive drains and forwarding wrappers preserve the checked
  result/state relationship through their actual normal-return paths.
- A probe result can pass through aliases and proven state-preserving code
  before its case is matched, without losing its authenticated relationship.
- Two pinned workers retain separate stores and communicate through copied
  messages; neither sender claims the recipient's continuation slots.
- Kernel preemption leaves the paused worker's Ash ownership unchanged while
  another worker progresses. Local yielding still selects among its own branches.
- Network scope completion settles producers and required channel work before
  releasing support; a persistent worker can remain alive afterward.
- An accepted publication remains accounted for after A begins finishing, and
  B's retained handling keeps completion pending after the queue becomes empty.
- Genuine end-of-input follows every accepted publication. The network cleanup
  returns only after receiver cleanup and any backing-access settlement finish.
- A bounded channel continues servicing B while A finishes its sends, rather
  than imposing a closing order that prevents the necessary receive.
- A sends to B and B sends back to A; completion follows the rooted causal
  obligations while both workers continue servicing messages and notifications.
- Child registration covers a message before publication, and parent accounting
  remains outstanding until the authentic completion acknowledgement arrives.
- A reply resumes an already-covered continuation without creating a completion
  dependency from a descendant back to its ancestor.
- Application quiescence is established while passive receive captures remain;
  only subsequent endpoint and backing settlement permits network cleanup return.
- Cleanup that produces a final message retains its producer obligation until
  that cleanup and its descendants finish.
- A recursive application drain preserves coverage and root closure, and its
  checked normal returns establish root emptiness without a decreasing count.
- Aliases and forwarding helpers preserve the matching record/network relation
  and authenticated result facts through their actual control.
- Child emptiness after local production closes justifies acknowledgement;
  root emptiness after root admission closes establishes stable application quiet.
- Shutdown summaries compose application quiet with actual worker and endpoint
  completion and channel settlement at the enclosing release boundary.
- Pure ledger registration queues one covered child before publication, and
  allocation remains fresh after earlier records retire.
- A closed, childless record retires locally while its parent dependency stays
  outstanding until the matching acknowledgement arrives. Duplicate retirement
  and acknowledgement leave unrelated work unchanged.
- The closed-root probe derives stable application quiescence from the current
  lists and invariant while remaining native notifications keep backing live.
- A proof plan for removal is reconstructed through its actual match branches,
  equality helper, proper-subterm recursive call, and returned constructor.
- `RemoveById` preserves whole retained entries and sequence order, including
  unchanged parent, phase, and children fields, on both result cases.
- Renaming, supported simplification, inlining, and specialization preserve or
  regenerate checkable derivations against the transformed linked Core.
- Transition preservation and current-state tracking compose the checked ledger
  lemmas with actual completion and the final resource-release summary.

Required negative cases include:

- A callback returns `Unit` with live slots and is presented as a valid drain.
- A pending arm advances and returns without recursively draining, or a suffix
  creates new work after the recursive drain has established quiescence.
- A forged or overridden quiescence result is used to authorize release.
- An old probe result is matched after a work-changing call, or an unanalysed
  external callee is incorrectly assigned no possible normal returns.
- A handler suffix or cleanup creates work after a successful drain, and an
  enclosing expression incorrectly retains the drain's postcondition.
- A retained capture depends on support that closes before its consumer, or
  restores under a different required exact interpreter.
- P and Q retain ordinary authority to the same resource without an admitted
  sharing contract, including through closures or evidence.
- A capture contains its destination's owning boundary, skips an outside
  completion, or abandons running cleanup.
- A transform substitutes a same-typed callback and reuses an obsolete drain,
  dependency, or interpreter proof.
- A remote worker attempts direct restoration with a copied key, or a proposed
  migration omits thread-affine support or duplicates execution authority.
- A local E snapshot is used to release network support while an external
  producer or an in-flight operation can still create work or access it.
- A send reports acceptance before acquiring delivery coverage, or receipt
  retires queued work before receiver control accounts for its handling.
- A temporary empty queue or a user payload is treated as genuine `End`, or
  an end marker overtakes an accepted but unpublished message.
- Channel backing is released after send completion or queue exhaustion while
  receiver cleanup, wake registrations, or another backing user remains active.
- Two local-empty observations certify shutdown despite bidirectional feedback,
  or both receive loops wait for `End` before either send polarity can close.
- A child message becomes visible before registration, or a stale, duplicated,
  or ordinary user-produced acknowledgement retires unrelated work.
- An independently productive callback or cleanup is classified as passive,
  or `AppQuiet` is incorrectly treated as final local-store completion.
- A finishing function's summary assumes causal coverage from a recursive call
  without establishing or admitting the channel and accounting invariants.
- A suspension wrapper's ordinary return or a forged `Finished` constructor
  is treated as actual local application completion.
- A stale child-empty result is used after another child is registered, or an
  old root-empty result survives closure that registers earlier accepted work.
- A publication uses a different record or network from the preceding
  registration, or application code bypasses accounting through a raw endpoint.
- An arbitrary ledger counter or done flag is treated as an admitted invariant,
  or unknown external control incorrectly preserves a protocol fact.
- A driver updates or probes from an obsolete ledger version, reenters an
  in-progress update from its old input, or replays an accepted output.
- Arbitrary cyclic or application-built lists are assumed to satisfy the finite
  private-ledger invariant, or changed collection code reuses an old proof.
- Application data is interpreted as a private completion envelope, or an empty
  pending-output list is treated as native transport settlement.
- A forged plan, arbitrary Boolean equality helper, or same-typed replacement
  receives a collection lemma without checking its actual definition.
- Removal keeps the correct identifier set but changes a retained record's phase
  or parent, reports `Found` for an absent key, or omits a reachable proof arm.
- An induction hypothesis is applied to the unchanged input, a possibly cyclic
  argument lacks the finite precondition, or lemma dependencies justify each
  other without an admitted induction rule.
- A transform drops an unrelated entry or changes the returned state but retains
  an old proof because its name, source origin, or node identifier survived.
- An interface-only claim, unsupported transform, or exhausted proof check
  supplies a release permission without a reconstructed derivation.

Preservation must relate typed Core, the active control stack, the resource's
owned capture forest, slot generations, branch authority, and closing execution.
Each move must preserve unique ownership and completion phase. A progress result
must state its library/host assumptions rather than infer termination from
these safety properties.

Any later disposable prototype needs separate authorization. Its question is
whether resource-plus-cleanup composition can validate these cases with less
new machinery than a dedicated task or closing-scope node. Retain a bounded
comparison and counterexamples as design evidence; discard experimental runtime
machinery unless a later proposal explicitly selects it for product delivery.

## Open questions

1. Is the candidate finite return relation sound and sufficiently precise for
   store aliases, mutual recursion, imported control, and handler reinstatement?
   How should validation bound its state space and retain probe freshness facts
   through callback substitution and specialization?
2. How should fresh root admission and retained control carry branch authority
   without adding a general task primitive or assuming that duplicable resource
   handles are safe to share between concurrent processes?
3. Which external interpreter contexts can remain protected during normal drain
   and outer abandonment, and what restrictions give the smallest useful case?
4. What authenticated resource payload and operations admit owned captures while
   preserving slot capacity, failure atomicity, administrative back-references,
   and nonescape? Generic cell semantics do not answer this question.
5. Which typed checkpoint coverage contracts would justify stronger gas or
   latency bounds, independently of source syntax and insertion machinery?
6. Which wait, channel, and host-operation settlement contracts are needed
   beyond the initial ready-checkpoint fragment? How should the two-worker FIFO
   provider establish publication, stable end-of-input, and backing settlement,
   and how should their summaries compose under independent validation?
7. Which captures can admit migration, and how should a handoff preserve store
   identity, fixed ports, external interpretation, and completion responsibility?
   Rehoming and whole-executor movement need their own comparisons.
8. Is the candidate protocol-fact abstraction sound and sufficiently precise
   for record parameters, aliases, dynamic key reuse, imported control, and
   parallel interference? How should it compose checked ledger lemmas with
   provider laws that still need admission? Relating descendant coverage,
   reply handoffs, passive service, and backing settlement
   must not assume that the local E/W domain proves representation invariants.
   Larger topologies, cancellation, and failing workers remain separate.
9. Are the restricted claim schemas and induction rules sound and sufficient
   for the concrete ledger? Can the stated `RemoveById` normal-return soundness
   theorem be established from the local checking rules and structural induction?
   How should bounded normalization, plan dependencies, and transformations
   preserve checkability without general proof search? The candidate needs an
   implemented checker; its metadata and remaining claim schemas stay open.
