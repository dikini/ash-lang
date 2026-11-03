# First Slice: Cleanup and Owned Close Rules

This record develops candidate rules for R7–R10 and their E8/E10 intersections
in the [catalogue](first-slice-catalogue-and-map.md#rule-catalogue). It builds on
the [cleanup trace](first-slice-cleanup-trace.md), [discard ownership
trace](first-slice-discard-ownership-trace.md), and [request/capture
judgments](first-slice-request-capture-judgments.md). The rules are design
work, not Ash syntax, a complete calculus, or permission to remove a current
check. The [specification](../../../spec/README.md) defines current behavior.

## Subjects and current boundary

A cleanup evaluates its action in the preceding context. After successful
preparation it owns one invocation, independent of copies of the action.
Normal body return saves its actual value, invokes the action with `()`, and
returns that value after the action finishes. Capture and resume preserve the
owner's phase and saved value. An owned discard instead closes the selected
capture without resuming abandoned expressions; contained live clauses
contribute their captures recursively. Cleanup owners start at most once, in
structural inner-to-outer order. A running action and an unfinished close remain
completion obligations. These are [current execution
rules](../../../spec/dynamic-semantics.md#scoped-cleanup-actions) and
[discard steps](../../../spec/dynamic-semantics.md#effect-handlers-and-completion).

Use `GAMMA; Phi |- J` below for an established judgment under its lexical and
behavioral assumptions. An action contract includes its callable identity,
instantiated `Unit -> Unit ! epsilon` type, actual captures and dependencies,
possible transitive requests and their conditions, and relevant control and
completion behavior. It is conditional on its stated entry context. A capture
contract identifies the particular selected owner, ordered control and nested
ownership, phases, and outside obligations. These descriptions do not select a
certificate format or assert that today's summaries contain all these facts.
A new composition consumes established contracts and checks its new premises;
it does not inspect or reverify an action, capture, or outside constituent.
Unknown relevant facts stay obligations. The rules below apply unconditionally
only when their premises are established.

## Introduce and complete one cleanup owner

The scope rule uses the initializer's actual normal result as the action. It
checks the body under a fresh invocation owner for that activation. `Phi_a`
contains facts about that actual callable and the context *after* initializer
return; it is not the initializer's entry state. `fits_action` relates each
covered normal initializer result to the action and body premises, preserving
its value, dependencies, context and conditions together. The action's latent
row already reflects handlers inside the action. `epsilon_init`,
`epsilon_body`, and `epsilon_action` are combined by the ordinary partial row
union, not by assuming all three execute on every path.

```sequent
J-Cleanup-Scope :=
  GAMMA; Phi |- init : (Unit -> Unit ! epsilon_action) ! epsilon_init ; B_init
  GAMMA, action; Phi_a |- callable(action) : Unit -> Unit ! epsilon_action ; B_action
  GAMMA, action; Phi_a, armed(o, action) |- body : A ! epsilon_body ; B_body
  o is fresh for this cleanup activation
  GAMMA; Phi |- fits_action(B_init, Phi_a, B_action, B_body)
  GAMMA; Phi |- cleanup_scope_premises(B_action, B_body, o)
  epsilon = epsilon_init union epsilon_body union epsilon_action
  ===>
  GAMMA; Phi |- cleanup(init, body) : A ! epsilon ; B_cleanup
```

`B_cleanup` must cover initializer requests and non-return before acquisition,
successful acquisition with one armed owner and the selected allocation
context, and the body's applicable behavior. In particular, a request in the
initializer cannot capture an owner not yet acquired. Initial preparation
failure publishes no owner. A handler confined to the body cannot discharge the
later invocation; its own handler rule accounts for body effects. The candidate
rule includes ordinary function, scope, row and dependency premises; it does not
claim that naming `fits_action` supplies a checking procedure.

For an established normal body-return case, the following rule describes the
required composition. `Start` is behavior, not a claim that the action has
already terminated at type-check time. `Run` retains the saved actual value
and its dependencies, the action's actual context, and the remaining
completion obligations. Its successful finish restores that value, not the
action's `Unit` result. Requests and non-return during the action remain in
`Run`; nested scopes use their own rules.

```sequent
J-Cleanup-Normal-Start :=
  GAMMA; Phi |- normal_case(B_body, value, state, deps, condition)
  GAMMA; Phi, condition |- owner_phase(o, armed, state)
  GAMMA; Phi, condition |- invocation_fits(B_action, state, action_context)
  GAMMA; Phi, condition |- saved_value_safe(value, deps, action_context)
  ===>
  GAMMA; Phi, condition |- normal_cleanup_case(o, value, deps) : Start(o, Run(B_action, saved(value, deps), return_saved))
```

A corresponding successful `Finish` discharges the **running** owner and
returns the same saved value with its relevant facts; it does not start that
owner again. Capture and resume transport armed or running phase, the selected
allocation context and saved value without duplicating or restarting them. A
running owner outside an inner action-local discard can still finish if its
continuation survives. These obligations and the runtime phases are distinct
from any proof that an action terminates or external release succeeds. See
[cleanup typing](../../../spec/static-semantics.md#scoped-cleanup-actions) and
[execution](../../../spec/dynamic-semantics.md#scoped-cleanup-actions).

## Build the owned close in structural order

For each covered source-handler selection, the [capture
rule](first-slice-request-capture-judgments.md#select-a-source-handler) supplies
an available ordinary capability `k`, its particular capture `C`, and outside
control `O`. A plan is a symbolic ordered composition of the owners actually
owned by `C`, not a list of all owners visible at discard. Each entry retains
its activation, phase, action contract or other boundary contract, and its
structural closing position. Let `P1 ++ P2` preserve inner-to-outer order.
The following candidate rules compose established component plans when a new
capture composition is formed. `capture_parts` is the new composition's
relationship between those already established components. If a capture is
already certified, reuse its established plan as-is; never traverse or
decompose that capture again to reconstruct its plan. Leaf rules introduce
plans from the applicable established local owner contracts:

```sequent
family owned-close-plan:
  J-Plan-Empty :=
    GAMMA; Phi |- capture_empty(C)
    ===>
    GAMMA; Phi |- close_plan(C) = []

  J-Plan-Compose :=
    GAMMA; Phi |- capture_parts(C) = inner, outer is an exhaustive, disjoint, ordered decomposition
    GAMMA; Phi |- close_plan(inner) = P1
    GAMMA; Phi |- close_plan(outer) = P2
    ===>
    GAMMA; Phi |- close_plan(C) = P1 ++ P2

  J-Plan-Armed-Cleanup :=
    GAMMA; Phi |- C is exactly the owned cleanup position (o, armed, action, B_action, position)
    ===>
    GAMMA; Phi |- close_plan(C) = [close_cleanup(o, action, B_action, position)]

  J-Plan-Other-Owner :=
    GAMMA; Phi |- C is exactly the owned boundary position (o, contract, position)
    o is neither a cleanup owner nor a clause owner
    GAMMA; Phi |- boundary_close_plan(contract, o, position) = P_o
    ===>
    GAMMA; Phi |- close_plan(C) = P_o

  J-Plan-Live-Clause :=
    GAMMA; Phi |- C is exactly the owned live clause position (k_inner, C_inner, position)
    GAMMA; Phi |- close_plan(C_inner) = P_inner
    ===>
    GAMMA; Phi |- close_plan(C) = [consume(k_inner, P_inner, position)]

  J-Plan-Consumed-Clause :=
    GAMMA; Phi |- C is exactly the owned consumed clause position (k_inner, position)
    ===>
    GAMMA; Phi |- close_plan(C) = []
```

Each leaf rule applies to exactly one owned position, not an arbitrary capture
that merely contains one. The decomposition covers all positions exactly
once in structural order, including nested captures; it cannot omit another
owner or count one twice. An armed cleanup at its position contributes its owner, action and contract;
other owned cells, registrations or excluded owners contribute their established
boundary close contracts at their own positions. A non-owning association adds
no owner. `consume(k_inner, P_inner, position)` contributes `P_inner` at that
position and consumes the nested capability exactly once. The meaning of
`next_close` and the quantification over plan entries includes nested plans in
structural order; neither is an instruction to traverse a certified capture or
reconstruct its plan. Their required summaries must already be established by
the relevant plan interface. The new composition
must preserve each nested clause's *structural* position, actual activation and
any relevant correlation with the selected request. `capture_parts` and the
exact-position facts are facts the new composition must establish using its
constituent interfaces; their names do not supply that derivation. In
particular, a lexical site alone does not identify a
recursive activation. An owned running cleanup, unfinished close, or unfinished
private work cannot be made closable merely by listing it. See the
[current ownership rules](../../../spec/static-semantics.md#effects) and
[close traversal](../../../src/core/capture/control.rs#L7032).

For a selected capture `C` and its plan `P`, `preserves(C, P, O)` must establish both that no running action or
unfinished close is abandoned *within* `P`, and that the surviving control
still reaches every required outside and running completion. An owner outside
`P` is not safe merely because it is absent from the plan: its scheduled
completion may lie in abandoned control. Conversely, an action running outside
`P` does not alone prohibit an inner discard when its completion survives.
This is a reachability obligation under the covered conditions, not a claim of
termination. The existing [outside-clause
check](../../../src/core/capture/control.rs#L5689) is one producer of a current
rejection, not a complete definition of this proposed judgment.

## Interpret each action and compute its row

For each action entry `a_i` at position `i`, let `H_i` be the ordered
interpreter context derived from the action's own certified local control,
remaining enclosing captured boundaries at `i`, and surviving discard
context. Each boundary uses its own lexical instantiation. `H_i` excludes a
body-local handler already passed; removed captured source or generated hook
handlers remain candidates for *compatibility checking* but are not restored
to execute the action. The position-specific context changes as enclosing
owners close. The [nearest-boundary
judgments](first-slice-nearest-boundary-judgments.md) describe candidate
selection; they do not by themselves prove cleanup compatibility.

```sequent
J-Close-Action-Context :=
  GAMMA; Phi |- close_position(P, i, action, H_i)
  GAMMA; Phi |- action_contract(action, B_action, epsilon_action)
  for each covered relevant request case r of B_action under H_i,
    GAMMA; Phi, condition(r) |- nearest_candidates(r, H_i, selections)
    each possible selected candidate is usable at position i
    each possible outward case preserves its request, row and crossing obligations
    GAMMA; Phi, condition(r) |- crossing_safe(r, selections, H_i)
  ===>
  GAMMA; Phi |- interpretable(action, H_i)
```

The request coverage must include transitive requests, local handling,
instantiation and applicable opaque-call assumptions. A known request that
passes all available boundaries may remain outward, with its effect and
crossing and completion obligations for an enclosing composition; it need not
already have a selected outer handler. A missing outcome, unknown necessary
request, or unresolved relevant equality leaves the premise unproved. A
removed nearest source or generated handler fails compatibility;
an outer same-instance source handler or cell does not replace it. Possible
generic coincidence must not be treated as inequality. A usable interpreter
does not establish payload or reply crossing by itself. Action-local handlers,
surviving source handlers and still-live unshadowed cells have the roles in
[current cleanup typing](../../../spec/static-semantics.md#scoped-cleanup-actions).

For the close effect, use the action's *whole instantiated latent row*, not an
enumeration of requests observed in one execution. Let `retained_i` contain
the applicable still-enclosing builtin cell instances at that position and any
additional retained interpreter instances supplied by established
outside-slice boundary contracts. For example, the current shared analysis
also accounts for retained Store `Probe` and `Drive`; their own rules remain
outside this slice. If their relevant contribution is not established, it is
an obligation, not an empty set. `remove_retained` performs the admitted exact
removals and respects open-row and lacks constraints. The action's own local
handling is already reflected in its latent row. Source-handler discharge
remains at each surviving source handler's own composition; it is not
subtracted as an implicit close-row step.

```sequent
J-Close-Row :=
  GAMMA; Phi |- close_plan(C) = P
  for each action entry a_i in P,
    GAMMA; Phi |- action_contract(a_i, B_i, epsilon_i)
    GAMMA; Phi |- retained_cell_and_external_instances(P, i) = retained_i
    GAMMA; Phi |- remove_retained(epsilon_i, retained_i) = delta_i
  GAMMA; Phi |- least_partial_union(delta_1, ..., delta_n) = epsilon_close
  ===>
  GAMMA; Phi |- close_row(P) = epsilon_close
```

For no owned actions, this union is empty, subject to any separately specified
boundary effects. A plan row is one case's contribution. When multiple
possible captures or instantiations reach one discard in a checking context,
the static discard row is the least partial union of the covered plan rows
and any applicable boundary contributions; it is not required to equal each
individual plan row. The current strict check groups action requirements by
discard and context and checks their combined row against the expected row.
Open tails and recursive or mutually dependent close rows may
require constraints or a fixed point; this schematic rule does not establish
that such a solution exists. Row inference alone does not prove interpreter
compatibility or safety. The current [requirement
producer](../../../src/core/capture/control.rs#L6855), [row
solver](../../../src/elaborate/cleanup_rows.rs#L392) and [strict row
check](../../../src/core/capture.rs#L3871) are distinct consumers and checks.

## Dependencies and the discard composition

For every covered plan and action, `dependencies_safe` must use actual value
and activation facts: action closure captures, the saved normal body value
where one exists, and each possible payload and actual interpreter reply. It
checks every relevant owner crossing and remaining lifetime using the
applicable resource or excluded-boundary contracts. A cell still enclosing an
action can be used until its close position; this does not permit its handle
or another dependent value to escape. The owner's trusted interpreter is an
admitted recipient under its own rule. A discarded body has no invented saved
result. Facts established for one reply, target or activation cannot be mixed
with another case to manufacture independence. See [cleanup
requirements](../../../spec/static-semantics.md#scoped-cleanup-actions),
[resource crossings](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
and [generic-cell replies](../../../spec/static-semantics.md#generic-cell-foundation).

```sequent
J-Owned-Discard :=
  GAMMA; Phi |- k is the active ordinary clause capability and is not Store-associated
  GAMMA; Phi |- incoming_structural_state(k) = available
  U(k, discard, available, consumed)
  GAMMA; Phi |- capture_cover(k, Cases) covers all applicable selections and activations
  for each case (phi, C, O, P) in Cases,
    GAMMA; Phi, phi |- the actual owner k is live and owns(k, C)
    GAMMA; Phi, phi |- surviving_control(k, C) = O and close_plan(C) = P
    GAMMA; Phi, phi |- preserves(C, P, O) and dependencies_safe(C, P, O)
    for each action a_i at position i in P,
      GAMMA; Phi, phi |- close_position(P, i, a_i, H_i) and interpretable(a_i, H_i)
  GAMMA; Phi |- epsilon_close is the least partial union of all covered plan rows and applicable boundary contributions
  ===>
  GAMMA; Phi |- discard(k) : Unit ! epsilon_close ; consumes(k), for each case (phi, C, O, P) schedules_under(phi, P, O)
```

The first three premises establish ordinary scope and structural availability
even if the capture cover is proved empty. Actual owner liveness is a separate
case-dependent fact; no rule infers a runtime selection from structural
availability. `capture_cover` must be a sound complete upper bound, including unknown
relevant alternatives, for this particular discard context. Each plan, outside
context, guard and activation remain correlated within its case. A missing
case or an unproved per-case premise does not establish the unconditional
conclusion; an infeasible case can be omitted only when its infeasibility is
proved. This is a symbolic check of the new composition using established
constituent facts, not a repeated inspection of those constituents.

The conclusion consumes only the selected capability and, in each case,
schedules its owned plan before that case's surviving clause continuation. It
does not assert that any action has already completed or that an abandoned
suffix runs. The following
candidate behavior facts describe one action's start and its *conditional*
successful finish; `P` is the remaining plan and `O` remains outside it:

```sequent
family close-action-completion:
  J-Close-Start :=
    GAMMA; Phi |- next_close(P) = close_cleanup(o, action, B_action, position), P_rest
    GAMMA; Phi |- owner_phase(o, armed, state)
    GAMMA; Phi |- interpretable(action, context_at(position))
    ===>
    GAMMA; Phi |- close_step(P, O) : Start(o, Run(B_action, no_saved_body_value, close_next(P_rest, O)))

  J-Close-Finish :=
    GAMMA; Phi |- running_close_action(o, B_action, P_rest, O)
    GAMMA; Phi |- normal_case(B_action, (), state, deps, condition)
    GAMMA; Phi, condition |- finish_premises(o, state, deps, P_rest, O)
    ===>
    GAMMA; Phi, condition |- finish_close_action(o) : discharged(o), close_next(P_rest, O)
```

The finish case is conditional on actual normal return; it does not establish
that the action returns. In successful execution each armed action finishes
before the next close position. If an action requests an operation, the
running state remains an obligation across capture and resume. Initial preflight failure occurs before owner
consumption; later internal failure can leave remaining actions unrun and does
not undo prior effects. These are not source-level recovery branches or a proof
of narrow correctness. The independent [usage
judgment](first-slice-continuation-use-trace.md#candidate-usage-judgments)
establishes the one-shot state transition but cannot establish the other
premises.

### Source-to-Core discard and owned-close correspondence

An ordinary source `discard` has no operand. It lowers to a Core discard node
with the corresponding **static** handler and clause-owner identities; its
close row describes all applicable owned-close cases, not a particular runtime
capture. The source and Core judgments must carry the already established
capture, plan and outside interfaces forward. A new composition establishes
its own relationships between them without reopening a certified clause,
capture, cleanup action or surviving continuation.

The [elaboration specification](../../../spec/elaboration.md) retains exact
handler and resume-owner identities. Current
[`synthesize_discard`](../../../src/elaborate.rs#L14048) resolves the active
clause, rejects a retained root and constructs a `DiscardNode` with
`ResumeUse::Consumed`, while deferring its cleanup row. Core
[node validation](../../../src/core/validate.rs#L15842) checks that annotation
and `Unit` result, and the [clause-contract pass](../../../src/core/validate.rs#L15995)
checks that the static pair names a clause. The independent capture, row and
control checks establish additional relationships; this structural node
validation alone does not prove owned-close safety. The candidate contracts
below are not current Core certificates and do not authorize dropping those
checks without a correspondence proof.

Write `Corr` for a guarded relation between the source and Core subjects,
values, control states, lexical instantiations and observations. It is not
identity of source and machine states. The static pair `(H,u)` identifies
the clause contract; each actual selection introduces a fresh dynamic owner
`k`. The node's `Consumed` annotation is a structural use fact and is not
itself a runtime owner or a proof that an actual transfer has happened.
`CaseObl(k,O)` attaches obligations to this **same already-bound** dynamic
case; an enclosing judgment must bind the witness and preserve its guards
when exporting the contract. Ordinary scope, type, row and structural usage
obligations retain their own scope and are not made conditional on runtime
reachability. In the transfer rule, `C` and `O` are the shared logical
projections of the related source and Core capture and survivor controls;
they do not require those controls to have identical physical representations.

```sequent
family discard-source-core-correspondence:
  J-Discard-Source-Core :=
    GAMMA; Phi |- the source discard is in its permitted ordinary clause scope, with static identities corresponding to (H,u)
    GAMMA; Phi |- incoming structural use is available and U(u,discard,available,consumed)
    the exact source and Core close rows are related under the admitted type and row substitution, including every applicable plan contribution and remaining row obligations
    the Core node is Discard(H,u,Consumed) : Unit ! epsilon_core
    J-Owned-Discard's complete capture cover and each case's plan, dependencies, interpreter and outside premises are established, or their scoped obligations are retained
    source and Core discard cases and their obligations are related by Corr without examining a certified constituent again
    O_outer contains every outstanding outer-scope obligation; O_scoped binds every clause and dynamic-case obligation with its original subject, witnesses and guard
    ===>
    GAMMA_core; Phi_core |- discard_corresponds(source,Core,H,u) [O_outer union O_scoped]

  J-Discard-Transfer-Source-Core :=
    GAMMA; Phi, phi |- Corr relates this actual selected source and Core clause case, with static pair (H,u) and the same fresh dynamic owner k
    GAMMA; Phi, phi |- the related live k owns the corresponding exact capture C and has the same surviving continuation O
    GAMMA; Phi, phi |- J-Owned-Discard supplies this same case's exact structural plan P, per-action interpreter and dependency facts, and surviving outside tickets
    GAMMA; Phi, phi |- source ownership validation and this Core discard preflight succeed, followed by this same successful transfer
    GAMMA; Phi, phi |- Corr relates the source logical close P before O to the Core scheduled close and outside control, including the zero-physical-owner case and the transferred nested tickets
    GAMMA; Phi, phi |- correspondence and transition evidence retain their case obligations O_transfer for this same k, C, P and O
    ===>
    GAMMA; Phi, phi |- correlated_discard_transfer(source,Core,k,C,P,O) [CaseObl(k,O_transfer)]
```

`O_outer` includes outer-scope and ordinary structural obligations; `O_scoped`
binds any clause, selected activation, local pattern and case witnesses under
their original guards. Neither a Core `Consumed` marker nor the static pair
establishes the dynamic selection, the actual live owner or a close plan.
The transfer case moves the same owned positions into their structural close
order, consumes `k` and transferred nested live clause capabilities once,
and preserves the same surviving outside tickets. A logical `CLOSE` need not
correspond to a physical completion frame when no physical close-owner frames
are scheduled. The close-end `Unit` enters the same survivor only after the
applicable plan completes; it is not a result from the abandoned body.

The [source rule](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
specifies successful ownership validation and preparation before scheduling
the owned close. The evaluator's [`discard`](../../../src/eval/machine.rs#L5254)
performs its applicable inspection and fallible reservations before consuming
the selected capture, then transfers and schedules owned positions. A
preflight failure is covered at its actual pre-transfer state, before this
consumption; dropping values during later transfer or close can record other
failures, with their own actual state and final-observation obligations. The
[failure cases](first-slice-failure-judgments.md#source-handler-request-resume-and-discard-cases)
must be related or retained as covering unknowns. The source success rule does
not itself specify a source transition corresponding to every internal Core
failure; neither this correspondence nor a row asserts that those failures are
impossible. `Corr` must relate the applicable permitted observations or retain
the missing failure-semantics obligation.

The source/Core relation for exact owned plans, activation identities,
per-position action interpretation, outside tickets, close rows and final
failure observations remains to be proved for all covered cases. In
particular, a may-capture, shared static pair, matching row or independently
valid clause does not supply that complete relation. Unknown cases remain
conditional and cannot justify a closed no-internal-error conclusion.

## Producers, consumers and remaining work

| Current producer or check | Result and required disposition |
| --- | --- |
| [Cleanup elaboration](../../../src/elaborate.rs#L16963) and [Core owner validation](../../../src/core/validate.rs#L13251) | Type the actual action and body and validate the owner and invocation shape. A scope judgment must preserve these identities and ordinary type/row facts. |
| [Control discovery](../../../src/core/capture/control.rs#L5768), [owned close](../../../src/core/capture/control.rs#L7032) and [removed handler check](../../../src/core/capture/control.rs#L6237) | Discover request, capture, phase and interpreter relationships for the current context. Candidate contracts must supply the facts needed by each new composition; a shared graph does not make their separate outcomes interchangeable. |
| [Close-row inference](../../../src/core/capture.rs#L3243), [solver](../../../src/elaborate/cleanup_rows.rs#L392) and [strict agreement](../../../src/core/capture.rs#L3871) | Produce contextual requirements, solve equations and authenticate rows. Preserve each result until an established rule supplies it to the same consumer. |
| [Dependency analysis](../../../src/core/capture/value.rs#L6184) and [payload checks](../../../src/core/capture/control.rs#L7587) | Check separate stored dependencies and crossing obligations; neither follows from the row or interpreter selection. |
| [Linked Core gate](../../../src/core/validate.rs#L13857) | Reconstructs relevant relationships on assembled Core when required. Independent validation remains authoritative; the new rules do not establish a replacement for every consumer. |

The open design includes a finite or otherwise checkable account of the
composition of certified capture plans, correlated possible requests, structural
positions and outside reachability; the provenance and stability of actual
reply and dependency facts; conditional polymorphic matching; row constraints
and fixed points; and boundary contracts for excluded owners. Establish the
full per-consumer correspondence before retiring a check. Separately justify the
completed rules against
the operational semantics and the intended narrow correctness guarantee.
Neither the current traces nor these candidate rules prove termination, a
complete program theorem, or that any current failure is external.
