# First Slice: Deriving Owned Close Obligations

This record refines the close-plan, outside-completion, interpreter and row
premises in the [close rules](first-slice-close-rules.md). The target is a
new composition using facts established for its constituents, not a pass
that scans their source, Core or control graphs again. The rules are candidate
judgments, not current Ash syntax, an implemented certificate or a proof of
soundness. The [specification](../../../spec/README.md) is current authority.
Store, regions and other excluded owners enter only through their own
established boundary contracts; this record defines no rules for them.

The [current cleanup](../../../spec/static-semantics.md#scoped-cleanup-actions)
and [discard](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
rules require more than a list of owned frames. A close must schedule the
right owned obligations in structural order, preserve required work outside
the capture, and account for the action requests and rows at each closing
position. In particular, an owner outside the capture can still be endangered
when its scheduled completion lies in abandoned control.

## Inputs and scope of the candidate rules

All judgments are conditional on `GAMMA; Phi` and a particular case guard
`phi`. A case preserves the correlation among its request, activation,
selected capability, capture, outside control, owner phases, actual action,
lexical instantiations and dependencies. A sound cover includes every feasible
case; an unknown case is not an empty set or an independent value. An exact
case describes every execution under its guard. A conservative may-case is a
possible alternative, not proof that it executes: admission must check every
such alternative unless its infeasibility is established.

The proposed inputs are established contracts for:

- each new control fragment: its ordered boundary interface, exact activation
  and owner facts, conditions, owned-close contribution, and the completion
  obligations whose continuation it may carry;
- each opaque action: its actual callable and lexical instantiation, latent
  row, applicable request-case cover and residual control, captured values and
  dependencies, and completion obligations under stated entry assumptions;
- a survivor route: the particular outstanding obligation and its required
  completion point, plus a conditional fact that the surviving continuation
  retains a path to that point without skipping it; and
- each excluded boundary: its acceptance or passing cases, ownership and
  close contribution, retained interpretation and row facts, and any other
  crossing or completion obligations needed by the composition.

These are required semantic interfaces, not assertions about the contents of
current callable summaries. A route says structural completion remains
available through the certified surviving control and its checked future
compositions; it does not say execution terminates, and it cannot be inferred
just from the owner being outside the capture. The exact representation,
producer and proof of route facts are open. A route that depends on an unknown
call, external scope or later discard carries those assumptions; without them
it does not establish unconditional preservation.

`U(k, discard, available, consumed)`, the actual incoming structural state
`available`, and the active ordinary non-Store clause premise are checked
independently of these runtime cases, including a proved empty cover. This
preserves the separate structural judgment described in the
[continuation trace](first-slice-continuation-use-trace.md). Successful
preparation for the runtime transfer is a different matter and is not proved
by structural use.

## Cleanup source-to-Core correspondence

A source cleanup evaluates its initializer once in the preceding context.
The current lowering first binds that result to a fresh callback binder; the
Core cleanup node names that binder, its checked body and its authenticated
action. Depending on the action row and elaboration, an allocation-context
query and binding can intervene before the Core node, and the action can use
a forwarding adapter. Those are actual conditional steps with their own
certified interfaces, not a cleanup initializer frame in Core. The query and
adapter are outside-slice inputs where applicable; their observable behavior,
dependencies and possible failures must be related to the source scope, not
assumed absent from an effect row.

Let `Corr_cleanup` be the system-level relation for the same source scope and
the exact constructed Core composition. It relates the entry contexts,
actual initializer result, callback binding, selected allocation context,
action invocation, body and completion cases, observations and their guarded
obligations. Its eventual proof is a property of the lowering and semantics;
the compiler does not prove system soundness for every program. The source
initializer, body, callback and any adapter are already certified children or
external contracts. `ScopeCleanup` binds the fresh owner and other case-local
witnesses without exporting them or dropping their guards.

```sequent
J-Cleanup-Source-Core :=
  GAMMA |- cleanup(init,body) has certified source judgment J_source using the same initializer and body judgments
  lower(init) and lower(body) supply their corresponding certified Core children and mapped obligations under the same scoped substitutions
  the constructed preceding Core binding binds fresh cb to the actual normal result of that initializer child
  the constructed Core Cleanup(cb,action_core,body_core) retains the same checked body and a certified action that invokes this cb with Unit
  each present intervening context query and action adapter has its established conditional contract and correspondence for this actual binding and selected context
  the new binding, optional query and cleanup composition satisfy their own type, row, scope, control and failure premises using the child contracts
  Corr_cleanup relates their complete source and Core cases or retains the corresponding scoped unknowns and obligations
  ===>
  GAMMA_core |- the exact constructed Core cleanup composition has the corresponding judgment and mapped obligations, with cleanup-local witnesses scoped by ScopeCleanup
```

The callback binder is fresh for the lowering, not a dynamic cleanup owner.
An initializer request retains its ordinary binding continuation; a failure,
non-return or abandonment before binding does not enter the cleanup node. A
query can request, fail or not return after the callback is bound and before
acquisition. In all these cases no cleanup invocation owner has yet been
published. Successful initializer evaluation or a well-typed callable alone
does not prove that later query, callable lookup, allocation or acquisition
preparation succeeds. If no query is present, no query execution is invented.

On a correlated successful Core acquisition, `Core-Cleanup-Acquire` uses the
actual binding, checks and prepares the action, creates a fresh dynamic armed
owner and enters the certified body. Its source counterpart acquires the same
logical invocation obligation under `Corr_cleanup`. Each successful execution
binds its own owner; a failed preparation creates none. The following rule
relates only that successful case, retaining its actual phase and entry state:

```sequent
J-Cleanup-Acquire-Source-Core :=
  GAMMA; Phi, phi |- Corr_cleanup relates this normal initializer result to cb's actual bound callable and any completed query to the applicable selected context
  GAMMA; Phi, phi |- the Core cleanup's callback lookup and acquisition preparation succeed for this same binding, yielding fresh armed owner o and state_o
  GAMMA; Phi, phi |- the corresponding source acquisition succeeds and Corr_cleanup relates the fresh owner, retained action, actual body entries and outside obligations
  GAMMA; Phi, phi |- the established action contract invokes this same callback and covers its actual later invocation context, or retains its scoped obligations
  ===>
  GAMMA; Phi, phi |- correlated_cleanup_owner(source,Core,o,armed,state_o) under ScopeCleanup(o,phi)
```

The owner's start changes its one armed obligation to running on a successful
normal body return or admitted owned close. The start contract records the
actual saved body value and dependencies, or the distinct close continuation;
the action's request, reply, failure and non-return cases keep that correlation.
On successful `Unit` return the finish contract discharges this same owner
and either restores the saved result with a sound post-state dependency cover
or advances the same owned close. Capture and resume move the same owner and
phase without another invocation. A no-reply path cannot abandon a running
owner or unfinished close. These facts use the established
[cleanup frame cases](first-slice-behavior-coverage-rules.md#bottom-up-frame-producers-and-case-coverage),
[phase tickets](#produce-and-transport-tickets-through-owned-close) and their
certified residuals; they do not recheck the action or body.

`J-Cleanup-Acquire-Source-Core` does not cover failed acquisition, start,
action, finish or disposal. `J-Cleanup-Source-Core` requires their correlated
case covers or explicit unknown obligations, including the actual point at
which a popped frame or changed counter can make a failure state differ.
Source and Core need not use identical intermediate machine steps. The
[source cleanup semantics](../../../spec/dynamic-semantics.md#scoped-cleanup-actions),
[source lowering](../../../src/resolve.rs#L10269),
[Core elaboration](../../../src/elaborate.rs#L16879) and
[acquisition](../../../src/eval/machine.rs#L3719) are the evidence to connect;
the correspondence, phase preservation and full behavior/failure cover are
not yet established by this candidate rule.

## Compose an owned plan

A plan judgment `Plan(C,P)` says that `P` covers exactly the owned close
positions of a particular capture component `C`, in inner-to-outer order.
It retains the case's activations, action contracts and phases. `P1 ++ P2`
composes previously established plans for two *newly joined* components;
it does not mean visiting the internal frames of a certified component. A
live nested clause contributes its capture plan at the clause position; a
consumed clause contributes no further capture. A non-owning reference is not
an owned leaf. Every leaf below is the complete atomic component described by
its premise, not any larger capture that merely contains it.

```sequent
family derive-close-plan:
  D-Plan-Empty :=
    C is the certified empty control component
    ===>
    GAMMA; Phi, phi |- Plan(C, [])

  D-Plan-Plain :=
    C is exactly a non-owning ordinary control position
    ===>
    GAMMA; Phi, phi |- Plan(C, [])

  D-Plan-Armed :=
    C is exactly the owned armed cleanup position (o, action, contract, position)
    ===>
    GAMMA; Phi, phi |- Plan(C, [cleanup(o, action, contract, position)])

  D-Plan-Cell :=
    C is exactly the owned live cell position (a, payload, cell_contract, position)
    the established cell contract supplies its close and applicable backing obligations
    ===>
    GAMMA; Phi, phi |- Plan(C, [cell(a, payload, cell_contract, position)])

  D-Plan-Closed-Clause :=
    C is exactly the owned consumed clause position k
    ===>
    GAMMA; Phi, phi |- Plan(C, [])

  D-Plan-Live-Clause :=
    C is exactly the owned live clause position (k, C_inner, position)
    GAMMA; Phi, phi |- Plan(C_inner, P_inner)
    ===>
    GAMMA; Phi, phi |- Plan(C, [consume(k, P_inner, position)])

  D-Plan-External :=
    C is exactly an owned excluded boundary position (o, contract, position)
    GAMMA; Phi, phi |- contract supplies its ordered owned plan P_o at position
    ===>
    GAMMA; Phi, phi |- Plan(C, P_o)

  D-Plan-Join :=
    the new composition splits C into C_inner and C_outer, exhaustively and without overlap
    this split preserves the certified structural position and nested ownership of every component
    GAMMA; Phi, phi |- Plan(C_inner, P_inner)
    GAMMA; Phi, phi |- Plan(C_outer, P_outer)
    ===>
    GAMMA; Phi, phi |- Plan(C, P_inner ++ P_outer)
```

The `consume(k,P_inner,position)` entry records a nested live clause at
plan-construction time. In the current evaluator, successful outer discard
transfer takes the nested capture and consumes its clause capability before
any scheduled close action runs; the entry retains the structural position at
which `P_inner` is to be executed. It does not require a second runtime
consumption when the close cursor later reaches that position. The
[discard transfer](../../../src/eval/machine.rs#L5438) is implementation
evidence for this distinction.

The split must be established from the composition's boundary interfaces;
its name does not prove exhaustiveness. An already established `Plan(C,P)` is
used as-is. An ordinary position with an empty owned plan can still carry the
only scheduled completion of an outside owner; the ticket check below must
account for it. A running cleanup, unfinished close or unfinished private work in
an abandoned owned segment has no armed-leaf rule; it is a blocking case, not
an empty plan. If the phase or ownership is unknown, retain an obligation
rather than selecting the armed or non-owning rule. Store-associated completion
is not converted into an ordinary discard: its separate boundary contract must
supply any applicable facts.

For a newly selected **ordinary source handler**, the following rule derives
the whole selected capture's plan from the crossed prefix's certified plan.
`prefix ++ h` is the ordered captured segment supplied by the existing exact
selection judgment, including the selected handler as its outermost position.
The ordinary source handler boundary is not itself a cell, cleanup, or live
clause owner. Its saved ordinary values retain their own dependency facts;
this empty owned-close contribution does not prove that those values are
independent. `C` is this selection's actual capture, not every execution of
the same source site.

```sequent
D-Plan-Selected-Source :=
  GAMMA; Phi, phi |- selects(r, K, selected(h, prefix, outside))
  h is the selected ordinary source-handler boundary
  GAMMA; Phi, phi |- selected_capture(r, h) = C and C = prefix ++ h
  GAMMA; Phi, phi |- Plan(prefix, P_prefix)
  ===>
  GAMMA; Phi, phi |- Plan(C, P_prefix)
```

This is the special case of `D-Plan-Join` and `D-Plan-Plain` for a source
boundary, not a replacement for builtin or excluded-owner contracts. The
prefix plan must already include its nested live captures. An uncertain
nearest boundary has one such conditional composition per covered source
selection; a may-selection member is not itself an exact `selects` premise.
This rule does not establish payload crossing or outside completion.

Elimination uses the certified plan's ordered *interface* at its next
position. These are conditional behavior rules, not another plan construction
or a traversal of the captured constituent. `P_rest` preserves every later
entry and outside context `O`.

```sequent
family eliminate-close-plan:
  D-Next-Armed :=
    GAMMA; Phi, phi |- next(P) = cleanup(o, action, contract, position), P_rest
    o is armed in this case and the action's invocation premises hold at position
    ===>
    GAMMA; Phi, phi |- step(P, O) = start(o, action, close_next(P_rest, O))

  D-Next-Live-Clause :=
    GAMMA; Phi, phi |- next(P) = consume(k, P_inner, position), P_rest
    GAMMA; Phi, phi |- the successful discard transfer has consumed this nested k and left P_inner pending at position
    ===>
    GAMMA; Phi, phi |- step(P, O) = close_nested(P_inner, P_rest, O)

  D-Next-Cell :=
    GAMMA; Phi, phi |- next(P) = cell(a, payload, cell_contract, position), P_rest
    the same activation a is live and the cell contract's close premises hold
    ===>
    GAMMA; Phi, phi |- step(P, O) = schedule_cell_close(a, payload, cell_contract, P_rest, O)

  D-Next-External :=
    GAMMA; Phi, phi |- next(P) = external(o, contract, position), P_rest
    contract supplies the applicable close step and its remaining obligations
    ===>
    GAMMA; Phi, phi |- step(P, O) = external_step(contract, P_rest, O)

  D-Plan-Done :=
    GAMMA; Phi, phi |- next(P) = end
    ===>
    GAMMA; Phi, phi |- step(P, O) = continue(O)
```

The cell leaf covers both current legacy and generic cell forms; their API
contracts and any external backing obligations remain distinct. `D-Next-Cell`
schedules close of the same activation and preserves the rest of the plan and
outside context. Release occurs only if execution reaches that position and
close succeeds; it is not a type-checking-time guarantee of termination.
`close_nested` advances to the already scheduled nested plan exactly once
before `P_rest`; it does not consume `k` again or resume the nested clause
suffix. This advancement is a logical view of the flattened close control,
not a claim that the evaluator executes a second nested-clause instruction.
An action moves from
armed to running when started. Only a *normal return* of that action can
finish its running completion and advance to `P_rest`. Its requests carry
that unfinished completion; divergence or terminal failure is not a
successful finish. Action-local scopes and discards use their own certified
rules. The behavior of other boundary entries is an explicit external input,
not an assumed empty effect or successful close.

## Derive preservation of outside completion

For one covered capture case, let `Need` be a certified exhaustive collection
of distinct outstanding completion tickets, each tied to its owner
activation and required completion point. The collection includes outer clause
completion, running actions, unfinished close and excluded-owner obligations
when applicable. It is not necessarily the list of owners in the capture.
For each ticket the composition must establish one disposition under the same
guard:

- `owned(t,p)`: the captured closure owns the eligible obligation and plan
  position `p` schedules that exact ticket once;
- `survives(t,r)`: the owner is outside the abandoned owned closure and an
  established route `r` retains its required completion point in surviving
  control; or
- `blocked(t)` or `unknown(t)`: a required completion is lost or its status
  cannot be proved. Neither establishes unconditional safety.

These dispositions are proof results, not labels chosen by the checker. In
particular a ticket whose owner is outside can still be blocked if its only
scheduled resume lies in the capture. A running action cannot use the owned
armed rule. It can use a survivor route when an inner action-local discard
leaves its actual continuation and completion intact. Distinct activations of
one source site have distinct tickets.

The following introduction rules construct the **local owner inventory** of
an exact control position. `Need_local` records tickets owned at that position;
it is not yet the complete inventory of an enclosing capture and its outside
control. Every ticket includes the particular runtime activation and its
required completion point. `refs(C)` is a separately certified interface for
completion points carried by the position on behalf of other owners: an
empty local inventory does not erase those references.

```sequent
family derive-local-tickets:
  D-Need-Live-Clause :=
    C is exactly the live ordinary clause position for actual owner k
    k owns its particular captured segment and must be consumed once
    ===>
    GAMMA; Phi, phi |- Need_local(C) = {ticket(k, consume)}

  D-Need-Armed-Cleanup :=
    C is exactly the armed cleanup position for actual owner o
    ===>
    GAMMA; Phi, phi |- Need_local(C) = {ticket(o, invoke_and_finish)}

  D-Need-Running-Cleanup :=
    C is exactly the running cleanup position for actual owner o
    its established control contract identifies the same running finish point
    ===>
    GAMMA; Phi, phi |- Need_local(C) = {ticket(o, finish)}

  D-Need-Cell :=
    C is exactly the live owned cell position for actual activation a
    its established cell contract identifies its release obligation
    ===>
    GAMMA; Phi, phi |- Need_local(C) = {ticket(a, release)}

  D-Need-Nonowner :=
    C is exactly a non-owning control position or an already consumed clause position
    ===>
    GAMMA; Phi, phi |- Need_local(C) = {}
```

An unfinished close or excluded owner contributes its own certified ticket
interface; it is not covered by `D-Need-Nonowner`. Running cleanup has a
completion ticket but no armed-close plan leaf, so it cannot be made
discardable by this inventory rule. The rules introduce required work, not a
claim that the work finishes. A consumed clause contributes no **new**
capability ticket, but its control may still carry a reference to an outside
ticket, which must remain in `refs(C)`.

A live clause also owns its captured segment. Its **whole** interface must
include the already certified nested segment's tickets and references, not
only the clause-local ticket. The following rule composes those interfaces at
that clause's structural position. A `merge_tickets` proof must preserve the
particular owner and nested activation identities.

```sequent
D-Need-Live-Capture :=
  C is exactly the live ordinary clause position for actual owner k and capture C_inner
  GAMMA; Phi, phi |- Need_local(C) = {ticket(k, consume)}
  GAMMA; Phi, phi |- refs_local(C) = refs_local
  GAMMA; Phi, phi |- Need_interface(C_inner) = (Need_inner, refs_inner)
  GAMMA; Phi, phi |- merge_tickets({ticket(k, consume)}, Need_inner) = Need
  ===>
  GAMMA; Phi, phi |- Need_interface(C) = (Need, refs_local union refs_inner)
```

The nested interface is an established input and is not reconstructed by
inspecting the captured segment. References carried by the clause position
itself remain in the conclusion under the same guard and activation.

For a newly formed control composition, the following rule combines complete
local inventories and reference interfaces. `merge_tickets` identifies two
references to the same actual ticket only with established owner-activation
equality; it preserves distinct obligations and their guards. It cannot merge
two activations merely because they arose at the same lexical site.

```sequent
D-Need-Compose :=
  the new ordered control composition consists exactly of C_inner and C_outer
  GAMMA; Phi, phi |- Need_interface(C_inner) = (Need_inner, refs_inner)
  GAMMA; Phi, phi |- Need_interface(C_outer) = (Need_outer, refs_outer)
  GAMMA; Phi, phi |- merge_tickets(Need_inner, Need_outer) = Need
  the join preserves refs_inner and refs_outer with their target activations and guards
  ===>
  GAMMA; Phi, phi |- Need_interface(C_inner ++ C_outer) = (Need, refs_inner union refs_outer)
```

The inputs must be complete for their stated components. A certified opaque
component supplies its interface as a whole; the join does not traverse it.
For a discard, the combined interfaces of the selected capture and relevant
outside control must cover all required tickets before `D-Safe-Completion`
applies. If equality of tickets, owner presence or an outside reference is
unknown, the join preserves alternatives or leaves an obligation; it cannot
invent an empty inventory.

### Introduce references to pending completion

An owner inventory alone cannot say where its completion is scheduled. A
binding frame can be non-owning while its saved remainder contains the only
structural use of an outside clause's capability. The checker therefore
retains a separate, case-indexed **use-site cover** with the already checked
usage judgment. A site is an abstract identity of a checked completion form;
it is not the form's implementation or a permission to inspect it again.
The cover records every structural `resume` or `discard` of that particular
capability in the checked constituent, including sites in branches that may
not execute. Each site retains its branch guard, owner identity and scope.
The identity is an abstract, scoped proof index. It need not expose a source
location or the declaration's implementation to a user of its type, and it
is hidden once no surrounding obligation can refer to it.
Ordinary capability-capture barriers are checked independently and do not
grant a capability to an opaque callable.

The following rules illustrate how the existing structural usage rules also
produce that cover in the *same* check. `sites(e,k)` is the cover attached to
the constituent's certified `U` judgment, and `s` is a fresh site identity
within the checked subject. `prefix_i` preserves the branch and lexical
context of each arm; it is not an assertion that the arm is reachable.

```sequent
family derive-structural-completion-sites:
  D-Sites-Preserve :=
    U(k, e, state, state) is certified with an established no-use-of-k fact
    ===>
    GAMMA; Phi |- sites(e,k) = {}

  D-Sites-Resume :=
    U(k, operand, state, available) and sites(operand,k) = {}
    U(k, resume operand, state, consumed) is established
    s is the fresh checked site identity for this resume
    ===>
    GAMMA; Phi |- sites(resume operand,k) = {site(s,k,resume)}

  D-Sites-Discard :=
    U(k, discard, available, consumed) is established
    s is the fresh checked site identity for this discard
    ===>
    GAMMA; Phi |- sites(discard,k) = {site(s,k,discard)}

  D-Sites-Sequence :=
    U(k, e1, state, middle) and U(k, e2, middle, out) are established
    GAMMA; Phi |- sites(e1,k) = S1 and sites(e2,k) = S2
    ===>
    GAMMA; Phi |- sites(sequence(e1,e2),k) = S1 union S2

  D-Sites-Match :=
    U(k, match(scrutinee,arms), state, out) is established
    GAMMA; Phi |- sites(scrutinee,k) = S0
    for each arm_i, GAMMA; Phi |- sites(arm_i,k) = S_i
    ===>
    GAMMA; Phi |- sites(match(scrutinee,arms),k) = S0 union union_i prefix_i(S_i)

  D-Sites-Perform :=
    U(k, perform op operand, state, out) is established
    GAMMA; Phi |- sites(operand,k) = S
    ===>
    GAMMA; Phi |- sites(perform op operand,k) = S

  D-Sites-Handler :=
    U(k, handle body with clauses, state, out) is established
    GAMMA; Phi |- sites(body,k) = S
    each clause's established boundary judgment excludes capture of this outside k
    ===>
    GAMMA; Phi |- sites(handle body with clauses,k) = S

  D-Sites-Cell :=
    U(k, cell_scope(initializer,body), state, out) is established
    GAMMA; Phi |- sites(initializer,k) = S_init and sites(body,k) = S_body
    ===>
    GAMMA; Phi |- sites(cell_scope(initializer,body),k) = S_init union S_body

  D-Sites-Cleanup :=
    U(k, cleanup(initializer,body), state, out) is established
    GAMMA; Phi |- sites(initializer,k) = S_init and sites(body,k) = S_body
    the action callable's established boundary excludes capture of this outside k
    ===>
    GAMMA; Phi |- sites(cleanup(initializer,body),k) = S_init union S_body
```

These are introductions for the newly checked forms, not a second traversal
to find uses. The sequence rule retains structural sites in the remainder even
if the initializer has no normal-return case: structural usage and behavioral
reachability are distinct. Guards and scopes remain attached to each site
through union. A specialization preserves the site's established identity and
substitutes its capability and guards together; distinct runtime activations
of the same checked site receive distinct owner identities. If an existing
opaque certificate cannot supply the applicable use-site cover or a proved
absence, its interface has an obligation rather than an invented empty set.
The `perform` rule concerns the operand; an operation request is not a use of
the current clause's capability. The handler rule concerns an **outside** `k`:
each clause introduces and checks its own capability separately. Cell and
cleanup preserve their checked initializer/body ordering; the cleanup action's
ordinary callable boundary must independently exclude capture of the outside
capability. None of these rules opens a checked clause or callable.

At execution boundaries the static site cover supplies *possible references*,
not a promise that a site executes. The new binding frame stores its certified
remainder. A pending `RESUME` frame is the active control for its own checked
site after the resume operand has started. The following rules attach a
reference to the actual ticket and physical control component in each case.

```sequent
family derive-completion-references:
  D-Ref-Pending-Binding :=
    C is the actual pending binding frame for the certified remainder e
    GAMMA; Phi, phi |- sites(e,k) = Sites under the saved instantiation
    GAMMA; Phi, phi |- ticket(k,consume) is live for this actual owner activation
    ===>
    GAMMA; Phi, phi |- refs_local(C) covers the guarded sites in Sites for ticket(k,consume)

  D-Ref-Pending-Resume :=
    C is the actual pending RESUME(H,k) frame introduced at checked site s
    GAMMA; Phi, phi |- ticket(k,consume) is live for this actual owner activation
    ===>
    GAMMA; Phi, phi |- refs_local(C) contains pending(site(s,k,resume), ticket(k,consume))
```

`D-Ref-Pending-Resume` does not itself say that evaluating the operand
terminates or that resume preparation succeeds. `D-Ref-Pending-Binding`
uses the saved remainder's certificate; it does not recheck that remainder
or turn each possible site into an actual event. If the remainder has other
outside-owner references, its complete interface must retain them as well.
The control composition maps each reference to the same ordered frame and
capture case in which it occurs. A reference to a site inside an opaque
already certified port must come from that port's interface.

For example, in an outer clause with a pending `let x = inner; resume x`, the
binding frame refers to the outer ticket through the certified remainder's
resume site. If an inner handler captures that frame and discards the capture,
the reference is inside the discarded component even though the outer owner
is outside. The reference's location identifies a lost candidate route; to
reject, the composition must also establish that no applicable route for the
same ticket survives outside or is discharged by an admitted close. Conversely,
an outside reference is not alone proof of a surviving route: its continuation
and all intervening covered cases still have to satisfy the route rules below.

### Derive survivor routes

For the in-slice owners, the structural point at which a ticket can be
completed comes from the corresponding operational boundary. It is indexed by
the actual activation and ready value, not just a source site or owner type.
The following rules introduce that point in a correlated state. They do not
assert that fallible preparation succeeds or that the preceding computation
reaches the point.

```sequent
family derive-ready-completion-points:
  D-Point-Resume :=
    the actual returned value v is at O = RESUME(H,k) followed by clause_control
    GAMMA; Phi, phi |- split_owner(clause_control,H,k) finds the same live captured owner k
    GAMMA; Phi, phi |- v satisfies that owner's established reply contract
    ===>
    GAMMA; Phi, phi |- ready_point(O, ticket(k,consume), resume(H,k,v))

  D-Point-Cleanup-Finish :=
    the actual returned value is Unit at the top running cleanup completion for owner o in O
    GAMMA; Phi, phi |- the same owner o is running and retains its saved return or close continuation
    ===>
    GAMMA; Phi, phi |- ready_point(O, ticket(o,finish), cleanup_finish(o))

  D-Point-Cell-Return :=
    the actual returned value v is at the top owned cell boundary for activation a in O
    GAMMA; Phi, phi |- a is live and the actual result crossing of a is admitted
    ===>
    GAMMA; Phi, phi |- ready_point(O, ticket(a,release), cell_return(a,v))
```

Each `O` includes the named point and its applicable surrounding control.
The resume point uses the [restore step](../../../spec/dynamic-semantics.md#effect-handlers-and-completion);
the cleanup and cell points use their respective normal completion steps. A
ready resume consumes the capability only when restoration succeeds. A ready
cleanup finish or cell return discharges its owner only through the applicable
successful transition. Preparation, allocation and internal disposal failures
remain in their own covered cases. An owned-close cell release uses its
established close-plan point instead of manufacturing a body result.

The next rules construct a route at a known completion point or across one
newly composed prefix. `continues(F,t,psi) to O` is an established conditional
fact that this prefix preserves the ticket's continuation on every relevant
normal or suspended path, and that each normal exit supplies the actual value,
state and dependency facts satisfying `psi`. `O(v,state,deps)` is the same
surviving continuation instantiated at that exit, not an unrelated context.
Later discards satisfy their own checks. This is not proof of termination. An
opaque prefix must supply its contract as an input; the composition does not
reopen it to decide whether the path survives.

```sequent
family derive-survivor-route:
  D-Route-Here :=
    GAMMA; Phi, phi |- ready_point(O, t, point)
    point is an admitted completion point for t under its established owner contract
    t is live in this case and the completion point accepts that ticket
    ===>
    GAMMA; Phi, phi |- route(t, O, required_completion(t))

  D-Route-Prefix :=
    the new surviving composition is F followed by the conditional continuation O
    GAMMA; Phi, phi |- continues(F, t, psi) to O
    for fresh v, state, deps, GAMMA; Phi, phi, psi(v,state,deps) |- route(t, O(v,state,deps), required_completion(t))
    ===>
    GAMMA; Phi, phi |- route(t, F then O, required_completion(t))
```

The following rules discharge two finite **new-composition** cases of
`continues` using an established control interface, rather than assuming that
every opaque frame preserves a ticket. `F`'s certified case cover is for the
same incoming activation and has already been established. `next_O` means the
normal exit passes its actual value, state and dependency facts into this exact
`O`, without consuming, moving or skipping `t`. `suspended_O` means a request's
pending continuation contains that same `O` and ticket, with their actual
ordering. A covered abandonment is acceptable
only when its selected close contract has already established that the
ticket's required continuation survives. In particular, the presence of
`t` outside a capture is not that proof.

```sequent
family derive-continuation-coverage:
  D-Continues-No-Request :=
    GAMMA; Phi, phi |- certified_cover(F, Cases)
    every case of Cases is a normal exit, non-return, or terminal failure
    for each normal exit in Cases, its correlated resulting control is next_O, t remains live, and psi holds of that exit's actual value, state and dependencies
    each covered non-return retains O and t, or an established close contract preserves the route through that same O
    ===>
    GAMMA; Phi, phi |- continues(F, t, psi) to O

  D-Continues-Requests :=
    GAMMA; Phi, phi |- certified_cover(F, Cases)
    for each normal exit in Cases, its correlated resulting control is next_O, t remains live, and psi holds of that exit's actual value, state and dependencies
    for each covered request case, its pending control is suspended_O
    for each covered reply, the certified residual has an established continues(residual, t, psi) to O under that reply's facts
    for each covered no-reply or abandonment case, its certified close and clause or interpreter outcome preserves the same O and ticket
    for each normal entry into O from such an outcome, t remains live and psi holds of that entry's actual value, state and dependencies
    for each later covered request in such an outcome, its certified residual continues with the same psi to that same O
    every remaining case is a covered non-return or terminal failure
    each covered non-return retains O and t, or an established close contract preserves the route through that same O
    ===>
    GAMMA; Phi, phi |- continues(F, t, psi) to O
```

The quantified premises are checked under each case's guard and its own
payload, reply, post-state and activation. They are sufficient rules, not a
claim that a row alone gives `certified_cover` or that a listed may-case
executes. Non-return does not reach `O` and does not discharge the ticket;
terminal failure follows its own failure/disposal contract and gives no source
completion guarantee. Neither is evidence that the owner is safely closed.
The request rule does not require a reply: it also covers checked no-reply
paths. A selected no-reply clause or close can reach `O` with a different
value or state than a resumed path, so its own normal-entry facts must satisfy
`psi`; merely preserving the location of `O` is insufficient. Its residual
premise covers later requests and their own no-reply
branches, not just the first suspended state. Recursive residuals need an
established guarded invariant that covers every later step. A close that
preserves a ticket by routing through a different context does not establish
the claimed route through `O`; it needs its own case-indexed route. If an
opaque residual, close or interpreter does not supply the needed
case, its premise remains an obligation. An infinite or recursive cover needs
the separate invariant and coverage justification; these finite rules do not
replace it. Apply `D-Route-Prefix` with `continues(F, t, psi) to O` and a
single conditional route certificate for that **same** `O` at every admitted
actual exit. A ready point established for one value or state does not prove
the corresponding point for another. This instantiates the already checked
route contract; it does not recheck the continuation for each exit.

The following introduction and elimination rules make the positive cases and
the all-ticket check explicit. `owner_plan_entry` identifies the actual owned
ticket and its unique entry; `route` is the established survivor fact described
above, including assumptions for any opaque continuation. They must be
supplied by the new boundary relationship or a certified external interface;
no rule here asserts they can always be inferred.

```sequent
family derive-completion-dispositions:
  D-Owned-Ticket :=
    GAMMA; Phi, phi |- selected_close_case(C, P, O)
    GAMMA; Phi, phi |- owner_plan_entry(t, C, P, position)
    t is eligible for the close form at position and appears there exactly once
    ===>
    GAMMA; Phi, phi |- disposition(t, C, P, O, owned(position))

  D-Surviving-Ticket :=
    GAMMA; Phi, phi |- selected_close_case(C, P, O)
    t's owner is outside the abandoned owned closure C
    GAMMA; Phi, phi |- route(t, close_behavior(P) then O, required_completion(t))
    ===>
    GAMMA; Phi, phi |- disposition(t, C, P, O, survives(O))

  D-Blocked-Captured-Use :=
    GAMMA; Phi, phi |- selected_close_case(C, P, O)
    t is the live consumption ticket of an ordinary owner outside C
    the certified remaining-use and reference interfaces cover every possible completion site for t
    every such applicable site is carried by a component of C that discard abandons
    the certified close plan P does not consume t or restore an abandoned component
    the surviving interfaces of O and P cannot introduce another completion of this actual t
    ===>
    GAMMA; Phi, phi |- disposition(t, C, P, O, blocked)

  D-Join-Tickets :=
    the new composition has the disjoint complete ticket inventories Need_1 and Need_2
    for each ticket in either inventory, its established disposition remains valid at the joined plan and survivor positions
    the join preserves guards, activations, unique owned positions and survivor-route assumptions
    ===>
    GAMMA; Phi, phi |- Need_1 union Need_2 has those dispositions for the new composition

  D-Safe-Completion :=
    GAMMA; Phi, phi |- selected_close_case(C, P, O) and Plan(C, P)
    GAMMA; Phi, phi |- Need covers every relevant outstanding ticket for this C, P, O and activation
    for each t in Need, GAMMA; Phi, phi |- disposition(t, C, P, O, owned(position)) or disposition(t, C, P, O, survives(O))
    no owned running action, unfinished close or unfinished private work is abandoned
    ===>
    GAMMA; Phi, phi |- preserves(C, P, O)
```

A composition can combine disposition maps from disjoint newly joined
fragments only when their ticket inventories cover the new outstanding set,
activations and guards agree, and the join preserves the route and unique plan
position for each ticket. An opaque fragment may instead supply its already
established conditional map. It is not valid to union an owned fact from one
case with an outside route from another. These are obligations on each join,
not permission to recompute a fragment's behavior.
Each disposition is indexed by the same capture, plan, outside context,
activation and guard as its use. A plan entry or survivor route established
for one case cannot establish preservation for a different plan or capture.

`D-Blocked-Captured-Use` is a sufficient structural rejection case, not an
inference from one may-reference. Its complete interfaces must rule out every
other applicable site and any completion supplied by an admitted external
boundary for the same activation. A source-site match is insufficient: another
execution of that site can have a different owner. The rule says that this
discard loses the checked completion route; it does not claim that execution
must terminate or that a missing route is a proof of a runtime event. If the
reference cover or outside interface is incomplete, the result is unknown,
not this rule's established `blocked` fact.

For a surviving ticket, the owned close plan runs **before** `O`. The route
premise therefore includes `close_behavior(P)`, including each action's actual
requests, nested discard and resulting state. An established route from `O`
alone is insufficient: the new close may disturb its entry assumptions or
abandon its required continuation. Derive the full route by composing the
certified plan behavior with the conditional `O` route using `D-Route-Prefix`.
If the plan cannot establish the matching entry and preservation conditions,
the survivor disposition remains an obligation. Failure and non-return stay
in their covered cases and do not establish that the ticket was discharged.

Disjointness concerns distinct obligation tickets, not references to them.
If both fragments mention the same outside owner, its single ticket must be
identified and assigned once while all references and route premises remain
accounted for. `D-Join-Tickets` applies after that agreement; it does not prove
that arbitrary summaries can establish identity or coalesce shared tickets.

`D-Safe-Completion` proves structural preservation conditional on the route
contracts, not eventual completion. A complete cover with a blocked or
unproved ticket cannot satisfy it. Conversely, no rule rejects an action-local
discard merely because an outside action is running: the relevant route must
be proved. The cited implementation has several checks, including
[owned-close discovery](../../../src/core/capture/control.rs#L7032) and an
[outside completion check](../../../src/core/capture/control.rs#L5689); neither
is claimed to publish this ledger today.

### Produce and transport tickets through owned close

The local inventory rules above describe tickets at a position. The following
rules say when the in-slice transitions create, move and discharge those
tickets. They are conditional on the same actual activation, state and guard
as the transition. An entry fact for an earlier state is not automatically a
fact about a later one. These rules use the
[cell](../../../spec/dynamic-semantics.md#scoped-cell-execution),
[cleanup](../../../spec/dynamic-semantics.md#scoped-cleanup-actions) and
[discard](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
steps; they do not add a source operation or recheck an action or body.

`loc(t,s)` identifies the unique control component or owned capture holding
the ticket in state `s`. The ticket is a judgment about required completion,
not a runtime object. `ticket(o,invoke_and_finish)` and `ticket(o,finish)`
are successive phases of the **same** cleanup obligation: starting replaces
the former with the latter; it does not create a second invocation. In each
rule, other tickets and reference facts are preserved only as established by
their own interfaces.

```sequent
family produce-completion-tickets:
  T-Clause-Select :=
    GAMMA; Phi, phi |- successful source selection moves this capture C into fresh live clause owner k at boundary b in s_next
    GAMMA; Phi, phi |- k is the ordinary capability for this same selection and actual activation
    ===>
    GAMMA; Phi, phi |- live(ticket(k,consume), s_next) and loc(ticket(k,consume),s_next) = b

  T-Clause-Resume :=
    GAMMA; Phi, phi |- live(ticket(k,consume), s) at the actual clause boundary owning C
    GAMMA; Phi, phi |- successful resume consumes this same k and restores C from s to s_next
    ===>
    GAMMA; Phi, phi |- discharged(ticket(k,consume), s_next) and C is restored in order

  T-Clause-Discard :=
    GAMMA; Phi, phi |- live(ticket(k,consume), s) at the actual ordinary clause boundary owning C
    GAMMA; Phi, phi |- discard preflight succeeds and the subsequent successful transfer consumes this same k and schedules P from s to s_next
    ===>
    GAMMA; Phi, phi |- discharged(ticket(k,consume), s_next) and P is scheduled

  T-Nested-Clause-Discard :=
    GAMMA; Phi, phi |- live(ticket(j,consume), s) at a nested live clause inside the selected outer capture C
    GAMMA; Phi, phi |- successful outer discard transfer from s to s_next consumes this same j and schedules its owned inner plan P_inner at its structural position
    ===>
    GAMMA; Phi, phi |- discharged(ticket(j,consume), s_next) and P_inner remains pending at that position

  T-Cell-Acquire :=
    GAMMA; Phi, phi |- successful cell acquisition from s creates fresh live activation a at boundary b in s_next
    GAMMA; Phi, phi |- the cell contract establishes a single release obligation for this a
    ===>
    GAMMA; Phi, phi |- live(ticket(a,release), s_next) and loc(ticket(a,release),s_next) = b

  T-Cleanup-Acquire :=
    GAMMA; Phi, phi |- successful Core cleanup acquisition from s creates fresh armed owner o at boundary b in s_next
    GAMMA; Phi, phi |- b retains the established action, actual callback binding and selected context
    ===>
    GAMMA; Phi, phi |- live(ticket(o,invoke_and_finish), s_next) and loc(ticket(o,invoke_and_finish),s_next) = b

  T-Cleanup-Start :=
    GAMMA; Phi, phi |- live(ticket(o,invoke_and_finish), s) at the actual armed owner and close or body-return position
    GAMMA; Phi, phi |- successful start moves that owner to running in s_next and installs its actual finish continuation F_o
    ===>
    GAMMA; Phi, phi |- live(ticket(o,finish), s_next) and loc(ticket(o,finish),s_next) = F_o

  T-Cleanup-Finish :=
    GAMMA; Phi, phi |- live(ticket(o,finish), s) at F_o for the same running owner
    GAMMA; Phi, phi |- the action actually returns Unit and the finish transition succeeds from s to s_next
    ===>
    GAMMA; Phi, phi |- discharged(ticket(o,finish), s_next) and F_o continues with its saved body result or close rest

  T-Cell-Release :=
    GAMMA; Phi, phi |- live(ticket(a,release), s) at the actual owned cell position for a
    GAMMA; Phi, phi |- the applicable normal-return crossing or owned-close premises hold for this case
    GAMMA; Phi, phi |- the release transition succeeds from s to s_next
    ===>
    GAMMA; Phi, phi |- discharged(ticket(a,release), s_next)
```

The clause selection creates its particular consumption ticket exactly once.
Resume and discard discharge that ticket only on their successful transfer;
successful outer discard also consumes the nested live clause tickets whose
captures it takes, while retaining their inner plans at their structural
positions. Discard then has the separately scheduled owner obligations in `P`. Preflight
failure proves neither consumption nor close; an implementation's malformed
post-take failure is a separate case in the
[resume failure table](first-slice-failure-judgments.md#source-handler-request-resume-and-discard-cases).
The acquisition rules apply only after successful preparation and publication;
failed preparation introduces no owner. Cleanup's callback was evaluated and
bound earlier, and the action may include an established allocation adapter;
see [Core cleanup acquisition](first-slice-behavior-coverage-rules.md#frame-transitions).
`T-Cleanup-Start` does not assert the action returns. A release in an owned
close uses the plan's `Unit` continuation, not a fabricated body result. A
failure or non-return does not discharge a ticket as a successful source
completion. Failure cases, including post-release disposal, retain their
actual failure states under the separate
[failure cover](first-slice-failure-judgments.md#introduce-and-compose-failure-cases).

The next rules transport a cell, cleanup or nested live ordinary-clause
ticket through the actual one-shot move. `C` is the same selected capture in
both transitions, and `t` names an owner inside that capture rather than the
newly introduced clause capability `k`. For a nested clause, its distinct
actual owner and recursively owned capture retain their established interface
at the same nested position. The capture interface already identifies the
local position `p` and its ownership; it is not rediscovered by inspecting `C`.

```sequent
family transport-completion-tickets:
  T-Capture :=
    GAMMA; Phi, phi |- live(t,s) and loc(t,s) = p within the selected segment C
    t is the cell release, cleanup-phase, or nested ordinary-clause consumption ticket for the same actual owner at p
    GAMMA; Phi, phi |- source selection successfully moves C into fresh live clause owner k, producing s_capture
    ===>
    GAMMA; Phi, phi |- live(t,s_capture) and loc(t,s_capture) = owned_position(k,C,p)

  T-Restore :=
    GAMMA; Phi, phi |- live(t,s) and loc(t,s) = owned_position(k,C,p)
    GAMMA; Phi, phi |- successful resume consumes the same live k and restores C in order from s to s_restore
    ===>
    GAMMA; Phi, phi |- live(t,s_restore) and loc(t,s_restore) = restored_position(C,p)
```

Neither move reacquires a cell, invokes a cleanup action, discharges its
ticket or duplicates its owner. An armed action stays armed; a running action
retains its finish continuation. A nested live clause retains its own distinct
capability and recursively owned capture without consuming either. A separate outside ticket stays outside
unless the same capture interface says otherwise. When a no-reply clause
discards, the owned-close rules decide whether each captured ticket can be
closed or whether its running completion blocks abandonment. A no-reply
clause can instead diverge while the capture remains live; it has not thereby
discarded it. A stale ticket, unknown phase or
unestablished location remains an obligation, not an empty inventory.

Now let `C(P,O,t,psi)` abbreviate the established judgment
`continues(close_behavior(P), t, psi) to O`. It concerns the very same `O`
and actual survivor ticket `t` as `D-Surviving-Ticket`. `psi` is the
conditional entry predicate for that continuation, with actual value, state
and dependencies. The following rules construct sufficient instances for a
**new** plan from its certified component interfaces. A previously certified
plan supplies its established conditional result; a later user does not
traverse its action list or replay these derivations.

```sequent
family close-survivor-producers:
  T-Close-End :=
    GAMMA; Phi, phi |- next(P) = end and t is live in the same surviving O
    GAMMA; Phi, phi |- a certified close-end cover includes every normal, failure, disposal and non-return alternative
    GAMMA; Phi, phi |- successful close-end completion passes Unit and its actual resulting state and dependencies to O
    GAMMA; Phi, phi |- psi holds of that correlated normal entry
    GAMMA; Phi, phi |- each covered non-return retains t and O, and every failure remains in its certified terminal failure and disposal case
    GAMMA; Phi, phi |- every other covered alternative has an established continues judgment to the same O, or is proved infeasible
    ===>
    GAMMA; Phi, phi |- C(P,O,t,psi)

  T-Close-Cell :=
    GAMMA; Phi, phi |- next(P) = cell(a,payload,cell_contract,position), P_rest
    GAMMA; Phi, phi |- t is a distinct live survivor and its required continuation is in the same O
    GAMMA; Phi, phi |- the certified cell-close cover includes every applicable success, request, non-return, failure and disposal alternative
    GAMMA; Phi, phi |- the certified cell-close step discharges ticket(a,release) on successful release and preserves t and O
    for each covered successful release state s_next, GAMMA; Phi, phi, release_case(s_next) |- C(P_rest,O,t,psi) at s_next
    GAMMA; Phi, phi |- the cell step's failure and disposal cases are retained separately
    GAMMA; Phi, phi |- every other cell-close case is a terminal failure, a non-return retaining t and O, or has established continues to the same O with psi
    ===>
    GAMMA; Phi, phi |- C(P,O,t,psi)

  T-Close-Nested-Clause :=
    GAMMA; Phi, phi |- next(P) = consume(k,P_inner,position), P_rest
    GAMMA; Phi, phi |- t is a distinct live survivor and O is its same required continuation
    GAMMA; Phi, phi |- the certified nested-close cover includes every applicable advancement, non-return, failure and disposal alternative
    GAMMA; Phi, phi |- the successful outer discard transfer already consumed this actual k once and left P_inner pending at position
    GAMMA; Phi, phi |- on successful advancement the close cursor enters P_inner before P_rest without consuming k again
    for each covered successful advancement state s_next, GAMMA; Phi, phi, advance_case(s_next) |- C(P_inner ++ P_rest,O,t,psi) at s_next
    every covered nonterminal case preserves or safely closes the same unfinished inner tickets
    GAMMA; Phi, phi |- every other nested-close case is a covered terminal failure, a non-return retaining t and O, or has established continues to the same O with psi
    ===>
    GAMMA; Phi, phi |- C(P,O,t,psi)

  T-Close-External :=
    GAMMA; Phi, phi |- next(P) = external(o,contract,position), P_rest
    GAMMA; Phi, phi |- the excluded boundary's certified contract applies to this actual owner and close position
    GAMMA; Phi, phi |- that contract supplies the complete external-step behavior followed by the certified P_rest and same O
    GAMMA; Phi, phi |- the supplied behavior continues the same t with psi to that O
    ===>
    GAMMA; Phi, phi |- C(P,O,t,psi)

  T-Close-Armed :=
    GAMMA; Phi, phi |- next(P) = cleanup(o,action,contract,position), P_rest
    GAMMA; Phi, phi |- t is a distinct live survivor and O is its same required continuation
    GAMMA; Phi, phi |- certified start and finish covers include all applicable success, non-return, failure and disposal outcomes
    every covered nonterminal case before successful start retains this armed owner and its ticket or has an independently admitted disposition
    every covered nonterminal start or finish alternative preserves t and the same O and retains or validly discharges this cleanup owner's applicable ticket
    every normal entry into O from such an alternative satisfies psi for its actual value, state and dependencies
    every later request in such an alternative has a certified residual continuing the same t and psi to the same O
    GAMMA; Phi, phi |- successful start installs running ticket(o,finish) and F_finish = finish(o) then close_behavior(P_rest) then O
    GAMMA; Phi, phi |- the certified action behavior continues both t and ticket(o,finish) to this same F_finish under their respective entry predicates
    GAMMA; Phi, phi |- every covered normal action result has the Unit representation by the action's established type and value contract
    for each covered normal Unit action result, successful finish discharges ticket(o,finish) and preserves t and O
    for each covered successful finish state s_next, GAMMA; Phi, phi, finish_case(s_next) |- C(P_rest,O,t,psi) at s_next
    GAMMA; Phi, phi |- start, action, finish and disposal failures are retained separately
    ===>
    GAMMA; Phi, phi |- C(P,O,t,psi)
```

The cell rule uses the cell contract for the **actual close position**, not
its lexical source site or an earlier root. The nested-clause rule composes
the already certified inner plan before the remaining outer plan, with the
same outside ticket and `O`; it does not resume the nested clause's abandoned
suffix or rederive the inner plan. Its advancement state precedes execution of
those plans, so the continuation does not close the inner plan twice. The armed rule requires the
action's complete certified behavior at its actual invocation entry and
interpreter context. In particular, `continues` for the action includes every
covered request, actual reply, no-reply outcome and non-return under
`D-Continues-Requests`. Both `t` and the running finish must survive: an
action-local discard may be admitted if its own already established close
and clause contracts retain the same `F_finish`; an outward discard that
abandons the running owner cannot satisfy this rule. The two continuation
certificates can share a proved fact but do not merge distinct tickets.
An external owner contributes only the certified boundary behavior and
preservation fact required by `T-Close-External`; its own semantics remain
outside this slice. If it cannot supply them, that case is an obligation.

The close-end contract covers both the implementation's immediate `Unit`
return when no owned close frames are scheduled and the `CloseCompletion`
frame when they are. `CLOSE` in the operational account denotes required
completion; it does not require allocating a physical frame in both cases.

The `for each` premises instantiate a single conditional suffix certificate
at the correlated symbolic success state. They do not recheck the suffix or
execute the action for each possible result. A failure case does not enter the
tail and does not prove `psi`. The close-end rule requires a complete case
cover for the close marker and its transition, including preparation and
disposal, rather than inferring a route from a successful case alone. A
remaining unknown cannot supply the required `continues` judgment merely by
being named; its own established contract must cover the ticket and exact
surviving continuation. The structural route remains conditional on
the separately retained failure and outside assumptions. For the agreed
closed-program no-error judgment, every applicable failure guard, including
preparation, action and disposal failures, must also be ruled out; a route or
a possible `Unit` return alone does not discharge it. An unknown action or
missing tail certificate remains a scoped obligation. The empty rule does not
claim the close was reached or completed.

For a concrete effectful action case, a builtin cell can answer a request
without a source-clause capture. The following rule propagates the two
continuation tickets over that one successful request and its actual reply.
The action's full cover must still include its other requests, possible source
handler interception, failure, non-return and no-reply branches.

```sequent
T-Action-Cell-Reply :=
  GAMMA; Phi, phi |- the certified action case requests r with pending F_finish and live tickets t and ticket(o,finish)
  GAMMA; Phi, phi |- nearest selection for this same r is the live builtin cell a, with no nearer accepting boundary
  GAMMA; Phi, phi |- the authenticated read or write succeeds with actual reply q, post-state s_q and reply dependencies d_q
  GAMMA; Phi, phi |- the transition preserves both tickets and F_finish in their actual positions
  GAMMA; Phi, phi |- the certified residual R for this same r, q, s_q and d_q continues both tickets to that same F_finish
  ===>
  GAMMA; Phi, phi |- this selected cell-reply case continues both tickets to F_finish
```

The cell's root and actual reply follow its established
[read/write cases](first-slice-behavior-coverage-rules.md#constructor-specific-delimited-ports);
the rule does not assume a read returns the initial root or that a write has
no dependency obligations. It does not establish that an action returns or
that a cell request cannot fail. For a selected source handler, use its
certified clause and port: each actual resume moves the same pending finish
and tickets back with its capture, and a no-reply case needs its own admitted
owned-close and surviving-clause route. Those cases must cover the same
request, owner and outside control. An interpreter outside the slice supplies
the corresponding conditional contract; it is not assumed to resume.

These producers still require system-level proofs that the ticket interfaces,
owner transitions and plan decompositions cover the operational semantics;
the conditional action interfaces must also be shown available from typed
Core. Recursive or unbounded action behavior needs an established guarded
route invariant, not a cyclic assertion. A generic unknown case does not
prove a route or no-error result, and the existing verification remains in
force until the resulting rules and their correspondence are established.

## Derive an action's interpreter cases

At an action's structural close position, the new composition supplies its
ordered applicable context `H`: action-local boundaries, still-enclosing
captured boundaries at that position, and surviving context, each with its own
lexical instantiation. A passed body-local handler is not in `H`. A removed
source or generated handler remains a *compatibility candidate* in its
original position, but is not restored for execution. A retained cell or an
outside-slice boundary contributes only the acceptance, passing and authority
facts established by its own contract.

For each action request case `r`, the [nearest-boundary rules](first-slice-nearest-boundary-judgments.md#candidate-composition-rules)
compose `accepts` and `passes` facts from inner to outer. Equality, inequality,
lacks and activation facts are conditional on their actual instantiation.
When equality is undecided, cover every possible match and pass outcome; lack
of proof of a match is not proof of a pass. An opaque suffix is not an empty
context unless its interface establishes that fact.

The following classification consumes one established exact nearest outcome.
A may-selection cover can supply alternatives to these rules, but every
possible member needs the applicable check; membership alone is not an exact
selection fact.

```sequent
family derive-close-interpreter:
  D-Action-Selected :=
    GAMMA; Phi, phi |- selects(r, H, selected(b, prefix, outside))
    b is action-local, surviving, or a still-live authenticated builtin interpreter
    actual request crossings and boundary obligations hold
    every covered actual reply, if supplied, satisfies its crossings
    no-reply, abandonment and completion alternatives remain covered
    ===>
    GAMMA; Phi, phi |- action_outcome(r, usable(b, prefix, outside))

  D-Action-Forwarded :=
    GAMMA; Phi, phi |- selects(r, H, outward(prefix))
    request identity, payload, residual, crossings and completion obligations remain in the outward contract
    ===>
    GAMMA; Phi, phi |- action_outcome(r, forwarded(prefix))

  D-Action-Removed :=
    GAMMA; Phi, phi |- selects(r, H, selected(b, prefix, outside))
    b is a removed source or generated handler
    ===>
    GAMMA; Phi, phi |- action_outcome(r, incompatible(b))

  D-Action-External :=
    GAMMA; Phi, phi |- selects(r, H, selected(b, prefix, outside))
    b is an excluded interpreter with an established applicable boundary contract
    the contract proves its authority, request crossings and completion obligations
    every covered actual reply, if supplied, satisfies its crossings
    no-reply, abandonment and completion alternatives remain covered
    ===>
    GAMMA; Phi, phi |- action_outcome(r, usable_external(b, prefix, outside))
```

The nearest removed candidate blocks the case: a later outer same-instance
handler cannot substitute. A forwarded known request is not a missing
interpreter proof; it retains its effect and obligations for the enclosing
composition. If the external interface has no applicable contract, selection
or crossing fact, the case remains an obligation. Unknown necessary requests,
unknown boundary behavior and unproved matching cannot be turned into a
successful empty outcome.

To establish `interpretable(action,H)`, apply these rules under every covered
request and selection condition, using `usable`, `usable_external` or
`forwarded` outcomes only, and establish all carried crossing and completion
premises. An incompatible feasible outcome rejects that abandonment. This
all-cases elimination checks the new context against established action and
boundary judgments; it does not reanalyze the action. The representation of
transitive request cases and their completeness at an opaque call remains
unresolved.

The following rules state that elimination. `request_cover` covers every
relevant request of this actual action under its stated entry assumptions;
`selection_cover` covers that request's nearest candidates and outward case
in this exact `H`. A case and its selection carry their own guards and
witnesses. `allowed` means precisely one of the usable, usable-external or
forwarded conclusions above, with its attached crossing and completion
obligations established or explicitly retained. It does not mean that a
selected interpreter is guaranteed to reply.

```sequent
family derive-interpretation-cover:
  D-Interpretable-Empty :=
    GAMMA; Phi, phi |- request_cover(action, H, []) is complete
    ===>
    GAMMA; Phi, phi |- interpretable(action, H)

  D-Interpretable-Cases :=
    GAMMA; Phi, phi |- request_cover(action, H, Requests) is complete
    for each request case (guard_r, r) in Requests,
      GAMMA; Phi, phi, guard_r |- selection_cover(r, H, Selections) is complete
      for each selection case (guard_s, selection) in Selections,
        GAMMA; Phi, phi, guard_r, guard_s |- action_outcome(r, selection) is allowed
    ===>
    GAMMA; Phi, phi |- interpretable(action, H)
```

The empty rule requires an established empty **request** cover, not an empty
row inferred from an absent summary. The nonempty rule also applies to an
unknown case only if its interface supplies a sound covering selection and
proves the required obligations for every represented outcome. A removed
nearest handler yields `incompatible` and cannot satisfy `allowed`. If its
case is proved infeasible it may be excluded; failure to find a witness is not
that proof. Conditional obligations may be retained only in a conditional
conclusion under the applicable boundary policy. The displayed unconditional
judgment requires them discharged. `H` is a parameter of the proof: an
interpretation fact established at one close position is not valid at another
position merely because the action is the same callable.

## Derive the close row

An action contract supplies its whole instantiated latent row `epsilon`, not
only requests observed on one path. Its action-local handlers already affect
that row. At position `i`, an established context contract supplies the
complete set of applicable retained builtin-cell instances and any excluded
interpreter instances, including Store facts where relevant. Unknown external
contributions remain obligations. Surviving source handlers discharge their
requirements at their own ordinary handler composition, not by silently
subtracting them here.

For a well-formed effect row, the following are conservative candidate
**close-row** removal rules informed by the current
[source solver](../../../src/elaborate/cleanup_rows.rs#L567) and
[Core row check](../../../src/core/capture.rs#L3871). The candidate
`close_remove` uses ordinary exact removal for a present member and preserves
the row for a proved-absent member. It is not the ordinary handler's exact
removal operation, which reports a missing target. `present_exact` requires
the exact instantiated member; `known_absent` requires established
inequality from every known member and either a closed tail or an applicable
lacks fact. An undecided equality or open tail that might contain the member
is neither case. The operation must also satisfy ordinary row well-formedness,
uniqueness and lacks constraints.

The candidate known-absent premise is stricter than the current structural
exact-removal implementation: for a closed row, the latter can report a
structurally missing member without proving inequality of unresolved generic
arguments. Whether and how such a result remains valid after specialization
is a correspondence question; different type variables do not prove unequal
instances. The candidate rule does not claim exact equivalence to current
admission.

A conditional result can preserve both possible instantiations without
declaring the type variables unequal. For the particular closed singleton row
`{E<T>}` and target `E<U>`, suppose `E` is an authenticated single-parameter
effect and `T` and `U` both have its declared parameter kind. Under `T = U`,
`close_remove` uses exact removal and produces `{}`; under `T != U`, its
known-absence case preserves `{E<T>}`. The proposed result can retain those two
guarded rows until a later instantiation establishes which case applies:

```sequent
D-Remove-Singleton-Conditional :=
  GAMMA; Phi, phi, T = U |- close_remove({E<T>}, E<U>) = {}
  GAMMA; Phi, phi, T != U |- close_remove({E<T>}, E<U>) = {E<T>}
  the equal and unequal conditions cover the applicable actual instantiations
  ===>
  GAMMA; Phi, phi |- guarded_remove({E<T>}, E<U>, [(T = U, {}), (T != U, {E<T>})])
```

The two premises reuse the exact-present and known-absent rules under their
respective assumptions. Neither case claims to occur. If the type system
cannot express or discharge these guards at a use, it must retain a sound
conditional obligation or use an independently justified conservative row;
it cannot silently choose the unequal case. A conservative upper bound alone
does not establish the required least synthesized close row: any checking or
weakening use must satisfy its own rule, and an unproved least-row obligation
remains. This example does not establish a
general algorithm for open rows, several potentially coincident members or
fixed-point row constraints. The finite closed-row construction below develops
the several-member case; open rows and fixed points still need their own
premises and the existing well-formedness and normalization rules.

For one bounded static composition, the two guarded results also determine a
least **unconditional** row. Assume there is exactly one close action, its
whole instantiated row is `{E<T>}`, its retained list is exactly `[E<U>]`,
and there are no other action or boundary row contributions. Restrict the
available closed row expressions for this example to `{}` and `{E<T>}`.
The following rule uses a separately established witness that an unequal
instantiation is feasible. It does not infer feasibility from failure to
prove equality.

```sequent
D-Singleton-Static-Row :=
  GAMMA; Phi, phi |- guarded_remove({E<T>}, E<U>, [(T = U, {}), (T != U, {E<T>})])
  the guarded cases cover every admitted instantiation of this close action
  an admitted instantiation satisfying Phi, phi and T != U is established
  the only admissible closed row expressions in this bounded comparison are {} and {E<T>}
  there are no other action or boundary row contributions
  ===>
  GAMMA; Phi, phi |- least_static_close_row = {E<T>}
```

Under either guard `{E<T>}` covers the required residual; at the established
unequal instantiation `{}` does not. Thus the conclusion is least in the
stated comparison, not merely a row weakened for checking. If inequality is
proved infeasible instead, the equal branch yields `{}`. If neither
feasibility nor infeasibility is established, this rule does not choose
either least result. Other row expressions, type equalities, escaping local
identities, open tails and multiple actions require their own proof; the
restricted comparison is not a general row-solver result.
The feasibility premise concerns an admitted abstract instantiation of the
guarded requirement; it does not prove that the cleanup action executes.

### Finite conditional removal from a closed row

This construction handles one action's fixed, finite **closed** row and one
fixed, finite list of retained interpreter instances at that action's actual
closing position. It consumes the action's certified whole latent row and the
context's certified retained list. The instances have already been mapped from
their own saved lexical contexts into the same case and are well kinded there;
neither mapping is reconstructed from the action body. The retained list is
known for this case, not assumed complete when an excluded boundary or an
unknown activation has not supplied its facts. The construction derives row
facts only: it does not prove that any candidate interpreter is usable or that
the close is safe.

Write `M = [M_1, ..., M_n]` for the known row members and
`R = [R_1, ..., R_m]` for the retained instances. Lists are only a finite
presentation: row order has no semantic effect, and the actual row is an
idempotent set. Compare **complete** effect identities and every ordered,
instantiated argument. Distinct authenticated effect identities are already
different. Equal or unequal facts previously established under this case's
assumptions are reused. For all other potentially equal pairs, form a finite
comparison vocabulary consisting of:

- each `(M_i, R_j)`, to decide which members are removed; and
- each `(M_i, M_k)` with `i < k`, to decide which surviving members
  coalesce after substitution.

An already settled pair is not split. Comparisons between retained instances
are unnecessary for this set-difference construction: repeating a retained
instance cannot remove an additional member. This does not assert that the
retained instances are different. A comparison means exact equality of the
complete instances in the **same** admissible instantiated world, including
their respective saved lexical substitutions and actual activation facts.
It is not equality of spellings, a guess that type variables differ, or a
new source-level inequality constraint. A settled fact must remain valid for
every admissible later substitution under its guard; a merely structural
mismatch between unresolved generic arguments does not settle the comparison.

For every assignment `b` of equality or inequality to the remaining pairs,
let `guard_b` be the original case condition conjoined with those decisions.
Use the established facts and positive decisions to form equality classes of
the `M_i`. Mark a class removed if one of its members is equal to a retained
instance under that branch. Let `delta_b` be the closed row with one
representative of each unmarked member class. Representatives are chosen by a
fixed presentation order only; every admissible realization of the guard has
the same normalized row regardless of that choice. This is a finite
construction with at most `2^(n*m + n*(n-1)/2)` assignments before settled
comparisons and pruning.

```sequent
D-Closed-Conditional-Removal :=
  GAMMA; Phi, phi |- the certified action row is the well-formed closed row {M_1, ..., M_n}
  GAMMA; Phi, phi |- R = [R_1, ..., R_m] is the complete retained list for this position
  each member and retained instance has its established kind, identity and lexical instantiation
  guards guard_b cover every admissible instantiation by deciding each unsettled relevant comparison
  for each guard_b, delta_b contains exactly one representative of each unremoved member equality class
  ===>
  GAMMA; Phi, phi |- guarded_close_remove(M, R) = {(guard_b, delta_b) for each b}
```

For any admissible substitution `sigma` satisfying one branch guard, normalize
`sigma(M)` by coalescing equal complete instances, then remove every instance
equal to a member of `sigma(R)`. The result is exactly the normalization of
`sigma(delta_b)`. This follows member by member: every actual equality with a
retained instance is represented by its decided comparison, and every pair of
equal surviving members is represented by its decided member comparison.
Conversely, an unmarked class has no retained match under that guard. This is
the mathematical correspondence that the eventual type-system rules must
justify against the [specified row operations](../../../spec/static-semantics.md#computation-types-and-effect-rows);
it is not a per-program execution or permission to verify the constituent
again. It is also not a claim that current Ash can express these guards.

All assignments are retained unless their infeasibility follows from the
established assumptions and equality constraints. In particular, failure to
find a witness or to prove equality does not prove inequality. A contradictory
assignment, such as two members both equal and unequal, can be omitted only
after the contradiction is established. An unresolved guard remains a
conditional case or an explicit obligation. Case-local owner witnesses and
identities cannot escape their scope in a published row. Substitution must
preserve kinds, scope, each comparison's two lexical environments and the
original lacks constraints; a later substitution may make two previously
distinct symbolic members coincide. It specializes the existing guarded
result, it does not recheck the action.

For example, let the closed row be `{E<T>, E<V>}` and the retained list be
`[E<U>]`, with the three arguments admitted at the declared parameter kind.
The following compressed guards cover the possibilities after exact
instantiation. A branch may be infeasible under additional assumptions; its
presence does not assert that it occurs.

| Guard | Normalized residual row |
| --- | --- |
| `T = U` and `V = U` | `{}` |
| `T = U` and `V != U` | `{E<V>}` |
| `T != U` and `V = U` | `{E<T>}` |
| `T != U`, `V != U` and `T = V` | `{E<T>}` |
| `T != U`, `V != U` and `T != V` | `{E<T>, E<V>}` |

The finite guarded result gives the exact candidate residual **per
instantiation**. It does not by itself give a representable unconditional
least row for all instantiations. Combining action rows and capture cases still
uses the partial unions and shared discard-row obligations below. If the
current type language cannot express a needed conditional result or a
well-scoped least common row, retain the obligation rather than publishing a
guessed row or treating weakening as synthesis. The construction does not
establish equivalence to current source or Core admission: their structural
removal and specialization behavior still needs the correspondence audit.

For an open row `{M_1, ..., M_n | rho}`, the closed-member result alone does
not decide removal from `rho`. The following sections give conditional tail
rules and a finite-equation construction. Neither adds a lacks fact or assumes
that current Core can represent an unresolved tail relation.

```sequent
family derive-close-row:
  D-Remove-Present :=
    GAMMA; Phi, phi |- present_exact(epsilon, I)
    removing exactly I from epsilon yields the well-formed row epsilon_rest
    ===>
    GAMMA; Phi, phi |- close_remove(epsilon, I) = epsilon_rest

  D-Remove-Absent :=
    GAMMA; Phi, phi |- known_absent(epsilon, I)
    ===>
    GAMMA; Phi, phi |- close_remove(epsilon, I) = epsilon

  D-Remove-Next :=
    GAMMA; Phi, phi |- close_remove(epsilon, I) = epsilon_1
    GAMMA; Phi, phi |- remove_list(epsilon_1, rest) = delta
    ===>
    GAMMA; Phi, phi |- remove_list(epsilon, I :: rest) = delta

  D-Remove-End :=
    ===>
    GAMMA; Phi, phi |- remove_list(epsilon, []) = epsilon

  D-Plan-Row :=
    for each action a_i in the certified plan P,
      GAMMA; Phi, phi |- action_row(a_i) = epsilon_i and retained_at(P, i) = instances_i
      GAMMA; Phi, phi |- remove_list(epsilon_i, instances_i) = delta_i
    the applicable external boundary contributions for P are established
    their partial union with all delta_i is defined and equals delta_P
    ===>
    GAMMA; Phi, phi |- plan_row(P) = delta_P
```

The actual plan and retained contexts for each action must remain correlated.
A different plan or activation can have a different row. When separate
feasible cases reach the same static discard in the same checking context, the
row is one least partial union over *all* covered plan contributions, not an
assertion that each plan has that whole row. Other context-specific constraints
and source-handler discharges still apply at their own boundaries. This
aggregation is a new composition of established row facts, not a replay of the
constituents. Case-local guards and witnesses do not escape into the result:
the resulting row and its constraints must be well scoped at the discard. If
the available row language cannot express a conditional contribution, a
well-scoped conservative union is needed; otherwise the row remains unproved.

```sequent
D-Discard-Row :=
  GAMMA; Phi |- Cases covers every applicable capture at this discard and context
  for each case (phi_j, P_j) in Cases, GAMMA; Phi, phi_j |- plan_row(P_j) = delta_j
  epsilon_close is the least well-formed partial union of the covered delta_j and required boundary contributions
  ===>
  GAMMA; Phi |- discard_row(Cases) = epsilon_close
```

If exact subtraction or row union is ambiguous, the candidate carries the
actual equality, lacks or row equation as an obligation. It cannot invent a
lacks fact or publish an unconditional row. If row variables are recursive,
the least solution must be established, along with any equalities and escape
checks; no fixed point follows merely from naming one. The current solver
iterates finite monotone union and exact-removal equations and separately
checks equality; exhaustion does not publish a result. This record does not
prove that its proposed symbolic inputs have a finite vocabulary, admit a
least solution, or can be represented by the present solver.

### Reuse a guarded least-row fact

There are two different least-row questions. A single static row must cover
all cases and substitutions admitted at its boundary. A later composition may
establish a parameter equality that restricts those cases, so the least row
under that stronger condition can be smaller. The first fact is still a
valid upper bound at the use, but it is not automatically the least row under
the stronger condition. Neither result permits inspecting the certified action
again.

For example, the earlier action row `{E<T>}` and retained instance `E<U>`
have the conditional results `{}` under `T = U` and `{E<T>}` under `T != U`.
If both instantiations are admitted, `{E<T>}` can be the least single static
row for the bounded example. At a use which establishes `T = U`, the retained
equal-branch fact gives `{}`. The use checks the new equality and instantiates
the existing fact; it does not derive the action's row again.

To make that reuse explicit, let `GuardedLeast(Phi, Cases, Rows)` be a
certified proposition for one discard and its complete case cover. Its
`Rows` entries are `(g_i, delta_i)`, where the well-scoped guards cover the
admitted type and row instantiations under `Phi`. For every admitted concrete
instantiation satisfying `g_i`, `delta_i` instantiates to a well-formed row
that covers **all** applicable capture and boundary contributions in that
same instantiation and is least among the rows admitted there. If guards
overlap, their instantiated results agree up to the established row equality.
An individual runtime capture case is not a substitute for that all-cases
requirement. Local owner witnesses may not escape through a published guard or
row.

```sequent
family guarded-least-close-row:
  D-Guarded-Least-Introduce :=
    GAMMA; Phi |- Cases is the certified complete capture and boundary cover
    the well-scoped guards g_i cover every admissible instantiation under Phi
    for each i and admissible instantiation sigma satisfying Phi and g_i, delta_i[sigma] is well formed and the least row covering all applicable Cases[sigma]
    overlapping guards establish equal instantiated rows under their shared conditions
    ===>
    GAMMA; Phi |- GuardedLeast(Phi, Cases, [(g_i,delta_i) for each i])

  D-Guarded-Least-Use :=
    GAMMA; Phi |- GuardedLeast(Phi, Cases, Rows)
    sigma is an admitted capture-avoiding instantiation respecting the certificate's scope and constraints
    (g_i,delta_i) is an entry in Rows
    GAMMA; Phi_new |- Phi[sigma] and delta_i[sigma] row ok in the new scope
    GAMMA; Phi_new |- g_i[sigma] and the applicable assumptions and obligations of that branch
    ===>
    GAMMA; Phi_new |- for every admitted closing tau, least_discard_row(Cases[sigma tau]) = delta_i[sigma tau]

  D-Guarded-Symbolic-Least :=
    GAMMA; Phi_new |- for every admitted closing tau, least_discard_row(Cases[sigma tau]) = delta_i[sigma tau]
    GAMMA; Phi_new |- delta_i[sigma] is an admitted symbolic row covering the symbolic Cases[sigma]
    for every admitted symbolic row epsilon covering Cases[sigma], GAMMA; Phi_new |- delta_i[sigma] is below epsilon under the specified symbolic row relation
    ===>
    GAMMA; Phi_new |- least_discard_row(Cases[sigma]) = delta_i[sigma]
```

`D-Guarded-Least-Introduce` states what the producer must establish; it does
not turn an arbitrary list of rows into a proof. The finite closed-row
comparison above supplies the guarded removal facts, and an established
least-union proof must combine every applicable action and boundary row for
each guard. The [open-tail relation](#retain-the-open-row-relationship) and
the finite recursive construction below can supply other necessary premises.
If `sigma` leaves parameters abstract, the new context and branch guard must
hold for every further admitted closing `tau`, and the resulting row must
remain well scoped and well formed. `D-Guarded-Least-Use` then reuses the
pointwise proof for each such `tau`. This does not by itself establish a
single **symbolic** least row under Ash's partial row operations.
`D-Guarded-Symbolic-Least` additionally requires a symbolic coverage and
leastness proof under the applicable row relation. Its universal premise is
a proof obligation, not an instruction to enumerate rows or an assertion that
semantic set inclusion is already an Ash row-subtyping rule. If `sigma` is
closed, the pointwise conclusion applies directly. An unproved future
constraint or symbolic leastness premise remains an obligation, not an
assumption made by this rule.
If no branch guard or least-union proof can be established, retain the
conditional relation or obligation. A conservative row can still serve an
independently permitted checking or weakening use, but it is not thereby a
proved least synthesis result. These are candidate type-level propositions;
current Ash does not yet retain the general guarded row contract.

### Conditional removal from an open tail

Let `{M | rho}` be a certified well-formed open row at this particular
position, and `I` a retained instance with its own certified lexical
instantiation. `M` denotes a finite known-member set, not an assertion about
the contents of `rho`. The following two rules give the tail cases for a
single removal. In both, the finite known-member construction above supplies
`M_rest` under the **same** guard; ordinary substitution and row formation
must preserve every existing lacks fact. The result row is published only if
it is well formed in the enclosing scope.

```sequent
family conditional-open-close-removal:
  D-Open-Tail-Absent :=
    GAMMA; Phi, phi |- {M | rho} row ok
    GAMMA; Phi, phi |- rho lacks I
    GAMMA; Phi, phi |- guarded_close_remove(M, [I]) has result M_rest
    GAMMA; Phi, phi |- {M_rest | rho} row ok
    ===>
    GAMMA; Phi, phi |- close_remove({M | rho}, I) = {M_rest | rho}

  D-Open-Tail-Present :=
    GAMMA; Phi, phi |- {M | rho} row ok
    GAMMA; Phi, phi |- rho = {I} union rho_rest and rho_rest lacks I
    GAMMA; Phi, phi |- guarded_close_remove(M, [I]) has result M_rest
    GAMMA; Phi, phi |- M_rest union rho_rest = epsilon_rest and epsilon_rest row ok
    ===>
    GAMMA; Phi, phi |- close_remove({M | rho}, I) = epsilon_rest
```

The first rule preserves a tail already known to lack the target. The second
requires an **established exact decomposition**, not an invented membership
fact or a fresh unrelated tail. In a well-formed input, `rho` also lacks each
known member of `M`; a purported branch where a matching known member and
`I` both occur in the tail is therefore inconsistent and can be removed only
with that proof. When a later admissible instantiation supplies a concrete
tail, exactly one of membership and absence applies to that instantiated
instance. A type-level conditional account may carry both guards and bind
`rho_rest` locally for the present case. It must retain the relation
`rho = {I} union rho_rest`, all original lacks and the witness's scope.
`rho_rest` is a row expression that may itself be closed; the equation is
metanotation, not a proposal to write an arbitrary row after a source tail.
The relation may not let `rho_rest` escape as an unrelated outward row variable.

For a retained list, compose these rules in order with `D-Remove-Next`,
propagating the **resulting** tail, its constraints and the case guard to the
next instance. Exact coincidence of two retained instances is handled under
their equality guard; removing an already removed instance uses the proved
absence branch. Different source names or a failed unification attempt do not
prove that guard. A branch whose tail membership or decomposition is unknown
remains a conditional row constraint or obligation. Neither `D-Open-Tail`
rule proves the requested fact merely by mentioning it.

For example, consider the open row `{ | rho}` and retained instance `E`.
Its pointwise result is `rho` when `rho` lacks `E`, and the remainder `rho_rest`
when `rho = {E} union rho_rest`. The original `rho` cannot serve as the exact
result in both cases: the instantiation `rho = {E}` must yield `{}`. Nor can
the fixed result `{}` serve all cases: `rho = {F}` for a distinct `F` must
yield `{F}`. A fresh, unconstrained outward tail does not state the necessary
relation either. Thus the current [row and scheme rules](../../../spec/static-semantics.md#computation-types-and-effect-rows),
which do not retain qualified membership or row-union constraints in schemes,
do not by themselves express this exact open-tail function for all
instantiations. This is a representability gap, not proof that no stronger
type-level relation could express it. Where the existing rules supply a
sufficient lacks fact or solved decomposition, use it; otherwise the relation
must remain an obligation or be addressed by an authorized semantic proposal.

### Retain the open-row relationship

For this slice, represent the unresolved relationship as a type-level
proposition `CloseRemove(R, I, S)`. Its intended meaning is that `R` and `S`
are well-formed rows and, for every complete effect instance `J`, membership
in `S` holds exactly when `J` belongs to `R` and `J` is not the exact
instance `I`. Equality compares the full instantiated identity and arguments.
The proposition is indexed by the same lexical substitutions and case
assumptions as the operation. It is a relation between rows, not a new
ordinary handler-removal rule or evidence that a handler exists.

The Core judgment carries this proposition and any evidence or outstanding
obligation at the boundary where the rows and witnesses are in scope. An
unknown `S` may be introduced as a scoped witness only together with the
relation; it is not an arbitrary independent output row. Publishing a result
outside that scope requires a well-scoped relation over the exported inputs
and result, or an explicitly quantified witness whose relationship remains
available to its consumer. Instantiation substitutes all three indices and
their guards together. The relation does not relax existing kinds, lacks,
partial-union or escaping-identity requirements.

The absent and present rules above establish particular instances of this
proposition. It also has the following use rule. `R'`, `I'` and `S'` are the
same rows and effect instance up to established equality under the current
case; mere similar spelling is insufficient.

```sequent
family close-remove-proposition:
  D-Close-Remove-Introduce :=
    GAMMA; Phi, phi |- R and S are well-formed rows
    GAMMA; Phi, phi |- for every instance J, J in S iff J in R and J != I
    ===>
    GAMMA; Phi, phi |- CloseRemove(R, I, S)

  D-Close-Remove-Use :=
    GAMMA; Phi, phi |- CloseRemove(R, I, S)
    GAMMA; Phi, phi |- R = R' and I = I' and S = S'
    ===>
    GAMMA; Phi, phi |- CloseRemove(R', I', S')
```

The first rule defines what evidence must prove; a checker need not enumerate
all instances if it has another sound derivation, such as the finite or
open-tail rules. The second transports an established proof, rather than
recomputing removal from a certified action. A consumer that needs the row
uses `S` under the proposition and its remaining assumptions. If the relation
cannot be proved at this boundary, it remains an obligation; a closed use that
requires the completed row cannot treat that obligation as proved. This is a
proposed extension of what types and propositions can express, not a claim
that current Ash schemes already carry it. A language change proposal must
specify its syntax, checking and evidence before implementation.

### A finite system of recursive close equations

A recursive set of **new composition** obligations can be represented by
row unknowns `X_1, ..., X_n` and equations whose expressions use certified
row inputs, union, and close-removal by established retained instances. Each
input carries its producer and subject, action or plan position, entry and
activation, guard, row and lacks constraints, and its own lexical substitution.
Each generated equation records the new composition and the input occurrences
it connects. This provenance keeps two equal-looking effects from different
cases from being combined as if their owner, handler or reply facts were the
same. It also allows a consumer to use a certified input row directly without
opening its producer or verifying it again.

For a fixed admissible instantiation, temporarily interpret each row as a set
of complete exact instances and each removal as set difference. Union and
removal by a fixed retained set are monotone in their row operand. Thus a
positive system built only from these operations has a pointwise least
solution. This set interpretation is a semantic account of the required row,
not permission to bypass the language's partial row-union or well-formedness
rules. Explicit equalities, lacks, local-identity escape and boundary
constraints must still hold for a publishable solution.

When the system has a **finite stationary vocabulary**, it has the following
finite symbolic construction. This condition means a finite set of equation
nodes, certified source-row occurrences, retained-instance expressions and
guard predicates, with substitutions and guard meanings preserved across
recursive references. For each fixed admissible instantiation, guard truth
and retained sets must be independent of the unknown rows being solved; a
membership test on an unknown `X_i` cannot choose an edge and still be assumed
monotone. A recursive occurrence whose relevant activation, instance
expression or guard changes without such a certified finite abstraction does
not satisfy the condition merely because its source text is finite. Strict
handler removal has its own exact-membership premise and failure behavior; it
is not silently changed into absent-tolerant close removal by this system.

First expand each nested union/removal expression into dependency edges.
An edge from `X_j` to `X_i` carries the finite retained set removed along
that step and the conjunction of its case conditions. A certified input row
occurrence supplies a seed at the corresponding node, with its own guard and
any removals between the input and that node. Then propagate a seed along an
edge by unioning the edge's retained set into the seed's accumulated removal
set and conjoining its guard. Coalesce only states with the **same** node,
source occurrence, accumulated retained set and guard conjunction under the
established equalities. Do not identify two owner activations, producer
subjects or substitutions merely because their rendered rows match. A path
contributes its source row after all removals accumulated on that path; the
node result is the guarded union of all its path contributions.

```sequent
family close-equation-paths:
  D-Row-Seed :=
    GAMMA; Phi, phi |- the certified source occurrence s contributes row S at node i
    GAMMA; Phi, phi |- its local accumulated retained set is K
    ===>
    GAMMA; Phi, phi |- row_path(i, s, S, K, phi)

  D-Row-Edge :=
    GAMMA; Phi, phi |- row_path(j, s, S, K, guard)
    GAMMA; Phi, phi |- the new equation has edge j to i with retained set K_edge and guard edge_guard
    ===>
    GAMMA; Phi, phi |- row_path(i, s, S, K union K_edge, guard and edge_guard)

  D-Row-Paths-Solution :=
    the finite stationary equation system and every seed and edge are established
    Paths is the saturation of D-Row-Seed and D-Row-Edge for that system
    for each node i, X_i is the guarded union of S close-remove-list K for its paths
    ===>
    GAMMA; Phi, phi |- Paths denotes the pointwise least solution of the equations
```

Each path's source, retained set and guard remain correlated. For every
admissible instantiation, a path contributes exactly the elements introduced
by its source that survive each removal on that path. Distributing removal
over union shows that all contributions introduced by any finite unfolding
are included, and none are added by the path construction. Every equation
solution contains those finite-unfolding contributions, so their union is the
least solution. This is a system-level justification obligation for the
candidate rules, not an instruction to replay a certified source's proof.

Saturation terminates for the stated vocabulary: each state is identified by
one node, one source occurrence, a subset of the finite retained-instance
vocabulary, and a conjunction drawn from the finite guard vocabulary, with
repeated conjuncts coalesced. A repeat adds no new state. Guards that cannot be proved infeasible remain;
they are not deleted just because a solver cannot decide them. If equality
of parameterized retained instances is unsettled, use the finite conditional
comparison construction above and retain each same-world branch. The bound
can be exponential; this is a finiteness argument, not a performance claim.
The proof does not apply to unbounded new instance expressions or guards, or
to a recursive owner relation lacking a sound stationary abstraction.

For example, with certified row inputs `S` and `T` and fixed retained sets
`K` and `J`, consider `X = S union (Y close-remove-list K)` and
`Y = T union (X close-remove-list J)`. The path construction yields
`X = S union (T close-remove-list K)` and
`Y = T union (S close-remove-list J)`: additional cycles only add removals
to an already included source contribution. This is a pointwise least set
solution even if `S` or `T` is supplied by an open tail. It is a valid Ash
row judgment only when the necessary tail relations, partial unions, kinds,
scope and lacks facts are also established. In particular, two distinct
unresolved open tails cannot be turned into one by this argument.

Finally, for every feasible capture case, compute its action-row equations
under that case's guard; combine their plan contributions and applicable
boundary contributions with `D-Discard-Row`. Solved equalities and
specialization must preserve case guards and owner provenance. A Core fragment
can carry a completed row judgment or a stated boundary assumption, but an
unproved guard, open-tail relation, row equality or nonrepresentable least
row is not a completed type. The path construction is not a general decision
procedure for arbitrary row constraints, arbitrary recursive guards or the
current implementation. The [current cleanup solver](../../../src/elaborate/cleanup_rows.rs#L437)
solves its own finite equations and checks additional equalities; identifying
an exact correspondence and proposing any new Core/type representation remain
separate work.

### Bound a nonstationary recursive case

The stationary construction does not cover a recursive reference merely
because its source expression is the same: the next reference can have a
different instance, guard or owner. One useful narrower case is a certified
finite family of *new* composition cases with a decreasing natural-number
rank. This can cover changing indices without identifying them.

Let `Case(c, a)` identify an equation case `c` with all of its actual static
indices and scoped witnesses `a`, including substitution, guard and owner
provenance. For a particular admitted closing substitution, the producer
supplies a finite, complete set `Reach` of feasible cases reachable from the
requested root. Its equations have the positive row operations and certified
source occurrences described above. Each dependency edge records both actual
endpoint cases and their correlation. The producer also supplies a rank for
each case, with every edge to a recursive dependency strictly decreasing that
rank. As in the stationary construction, guard truth and retained sets are
fixed for that closing substitution and do not depend on the rows being
solved. A recursive reference outside `Reach`, an unrepresented feasible branch,
or an edge without the rank fact leaves the family incomplete.

```sequent
family ranked-close-equations:
  D-Ranked-Close-Solution :=
    GAMMA; Phi, phi |- Reach is a finite complete family of reachable equation cases for the requested root
    GAMMA; Phi, phi |- every case has its certified source contributions and all its correlated dependency edges in Reach
    GAMMA; Phi, phi |- rank : Reach -> Nat and every dependency edge from c to d satisfies rank(d) < rank(c)
    GAMMA; Phi, phi |- each case row is its guarded union of source rows and the rows of its dependency cases after their recorded close removals
    GAMMA; Phi, phi |- X is obtained by evaluating these equations in increasing rank
    ===>
    GAMMA; Phi, phi |- X is the pointwise least set solution for Reach
```

The justification is induction on rank. Every dependency of a case has
already received its least row; union and removal by fixed retained instances
are monotone in those rows. The equation therefore determines that case's
least row, and the root follows without folding different indices into one
stationary case. The proof is about the equation family, not execution
termination: an action may diverge or make other requests in its established
behavior.

Finiteness, coverage and decreasing rank are requirements on the producer,
not facts inferred from a finite syntax tree. A bound for each closed
instantiation need not give a single finite symbolic representation for all
instantiations. Publishing a symbolic Core row additionally requires a
well-scoped representation and the existing row, equality, lacks and escape
premises; otherwise carry the guarded pointwise fact or an obligation. This
rule reuses the certified contributions for each recorded occurrence. It does
not open their implementations or recheck them while expanding the new
composition equations. Unbounded, cyclic or unknown families that cannot
meet these premises still need the stationary construction or another
justified interface.

## Discard admission and examples

The [owned-discard rule](first-slice-close-rules.md#dependencies-and-the-discard-composition)
consumes the structural capability once and applies the following checks to
every correlated covered case: its exact `Plan`, `preserves`, action
interpretation and value-dependency/crossing obligations. `D-Discard-Row`
supplies the single row after all cases have been covered. A missing plan,
route, interpreter outcome, external fact, value-dependency proof or row
solution prevents an unconditional conclusion. A proven empty runtime cover
makes those case checks vacuous, but does not discharge the independent
ordinary scope and structural availability premises.

A successful [E-Discard](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
consumes the live owner and schedules the ordered close before the surviving
clause continues. It does not itself establish that actions have finished.
Only successful execution of closing discharges their obligations; initial
preparation failure precedes transfer, and a later internal failure need not
run remaining actions or undo earlier effects. These rules neither prove that
such failures are external nor establish termination.

Consider an outer `A` clause whose only `resume` is in the pending remainder
of a `B`-handled computation. A `B` discard whose capture includes that
remainder has an outside `A` owner but loses its scheduled completion. Its
`A` ticket cannot use `D-Surviving-Ticket`; admission fails. Moving the `A`
resume after the entire inner `B` handler leaves that continuation in the
surviving context, allowing the route to be established when the other
premises hold. The [negative diagnostic case](../../../tests/effect_diagnostics.rs#L210)
and [owned-clause cases](../../../tests/effect_diagnostics.rs#L163) illustrate
the distinction; the matching [accepted boundary case](../../../tests/effect_typing.rs#L235)
checks the resume-after-handler arrangement.

For interpreter position, suppose a cleanup action requests `Log` and the
nearest `Log` handler at its close position is captured and removed. The
removed case fails even if another `Log` handler is outside. If that inner
handler has already been passed before the cleanup's closing position, it is
not a candidate; a surviving outer handler or a forwarded outward `Log`
request can be used according to its own contract. The [paired execution
cases](../../../tests/cleanup_abandonment.rs#L302) distinguish those
positions, and the [imported function](../../../tests/cleanup_abandonment.rs#L126)
shows a known outward close effect handled by a caller. They were inspected,
not run for this record.

If two feasible plans for the same discard require `{A}` and `{B}`, their
individual plan rows remain `{A}` and `{B}` and the static discard row must
cover their least partial union `{A, B}`, subject to the ordinary row rules.
This example is a consequence required of the candidate composition, not a
claim that a new test or a general row solver has been implemented.

## What the derivation still needs

The rules give introductions, conditional composition and elimination from
specified inputs; they do not establish that those inputs exist. In particular,
current imported callable summaries are not shown to expose exhaustive
correlated ticket inventories, survivor routes, ordered close-plan interfaces,
complete transitive request cases, or the context-dependent retained-instance
facts used above. Source inference for those facts, mutually recursive cases,
unknown callbacks, conditional type equality and external-owner contracts
remain open. The existing graph and linked validator still perform required
checks and serve other consumers; no check is shown removable here.

The soundness of ticket coverage, uniqueness and survival routes; plan and
activation preservation; interpreter selection; row fixed points; actual value
crossings; and correspondence with execution needs separate system-level
justification. The examples do not prove that justification or the intended
narrow correctness guarantee.
