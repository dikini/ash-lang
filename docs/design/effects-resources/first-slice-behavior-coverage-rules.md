# First Slice: Behavioral Coverage and Composition

This record develops the open behavior-interface problem in the
[rule-resolution status](first-slice-rule-resolution.md). It gives a semantic
coverage relation, symbolic case rules, a recursive summary rule and handler
and resume transformations. It builds on the existing
[request/capture](first-slice-request-capture-judgments.md),
[nearest-boundary](first-slice-nearest-boundary-judgments.md),
[normal-return](first-slice-normal-return-judgments.md),
[sequencing](first-slice-request-sequencing-judgments.md), and
[effect/completion](first-slice-effect-completion-rules.md) records. These are
candidate judgments, not Ash syntax, an implemented checker, a completed
calculus or permission to remove current checks. The
[specification](../../../spec/README.md) is authoritative for current Ash.

The question is how a checked fragment can publish a reusable upper bound on
its control behavior so that a new composition checks only its new
relationships. The producer establishes a fragment's contract once; a consumer
instantiates its certified interface, not its body or a graph representing
that body. Typed Core must retain complete types and the judgments needed for
this slice. The rules below do not select their storage format, require source
annotations, or waive current independent Core validation. General function
and data typing and excluded resource families remain outside this slice; their
certified contracts and outstanding assumptions remain inputs.

Effect and resource behavior is composed through the common proposition and
contract judgments. An operation declaration supplies its applicable request
and reply requirements; a particular handler supplies its own certified
behavior and must satisfy the applicable operation contracts. A resource
transition supplies its applicable behavior, authority, dependencies, control
and failure facts. The checker applies those contracts to the same actual
cases; it does not dispatch to a separate typechecker for each effect,
operation or resource. An operation declaration is not by itself a proof of
its handler's implementation.
An effect row is a coarser projection of requirements, not a complete account
of those behavioral facts. The
cell-labeled derivations below are concrete contract instances and evidence
for correspondence with the current cell implementation. They do not make
cells special to the type system or authorize a separate verification pass.
The correspondence showing that the general contract application accounts
for each concrete behavior remains to be established.

## Subjects and coverage

A **world** `w` records the relevant lexical instantiation, particular dynamic
activations, ordered control and owner phases, value dependencies and entry
state. It is an index of a judgment, not an Ash value or an existential source
package. A case binds fresh local witnesses `z`; its guard and facts `phi(w,z)`
refer to that same world. An owner name is not by itself a runtime activation.
A different request state, reply state or final return state is not identified
with the entry state. A historical entry fact does not prove a postcondition.

A boundary behavior describes a possibly infinite **interaction tree**. It is
metanotation for observable control relationships, not a required runtime tree
or Core data structure. Its relevant alternatives are:

- `return(v, state, deps)`: this fragment normally returns that actual value
  with the correlated resulting facts;
- `request(r, K, R)`: the actual exact request and payload, its ordered pending
  local control `K`, and a reply-indexed residual contract family `R`;
- `nonreturn`: a covered execution that does not normally return, without
  treating divergence as completed cleanup;
- `failure(origin, disposal)`: an internal failure together with a covering
  contract for the applicable subsequent disposal and final observation; and
- `unknown(U)`: a declared upper bound `U` on any relevant alternatives whose
  structure or facts are not established more precisely.

A request does **not** promise a reply. Its interpreter may resume, abandon
or fail, or may itself not return. A source handler's clause can discard its
capture and then return a value: the handler's result is not a reply to the
abandoned request. An exposed request is considered at the composition
boundary after the fragment's certified local boundary relationships; its
local control still describes the boundaries crossed before that point. The
selection and internal-handling facts needed to obtain that view must already
be established. Other in-slice and excluded interpreter behaviors remain
conditional on their own contracts.

For a covered request, `R(h, q, state_q, deps_q)` is conditional on the
**same** request case, an admissible selected interpreter context `h`, its
actual reply `q` and post-reply facts. `h` includes the selection and any
clause continuation needed at the fragment's boundary. `R` covers behavior
following that reply, including later requests and possible non-return or
failure. It need not be deterministic or finite. No premise says that `h` is
selected or that it replies. A handler's captured segment up to its own
boundary is a different subject from a residual of the **whole** enclosing
initializer; the handler rules below keep those boundaries separate.

Write `covers(B, E)` when behavior contract `B` covers concrete interaction
behavior `E`: for every applicable finite observation of `E`, one case of `B`
represents the **same** entry and all relevant observed request, control,
value, owner, dependency and state relationships; after each admissible reply
its corresponding residual covers the continuation. Infinite execution and
failure/disposal must also be represented by an applicable non-return,
failure or unknown alternative. Cases are upper bounds, not evidence that any
member occurs. A complete empty normal-return cover proves only that there is
no normal return under the stated assumptions. A missing case, unknown outcome
or absence of a summary proves no such fact. Failure origins and disposal
outcomes are distinct; an origin does not fix the final host report.

A behavioral certificate has the schematic form
`GAMMA; L, entry |- e : A ! epsilon ; B [O]`. `L` contains established stable
assumptions and `entry` describes the initial world. `O` is a set of scoped
obligations. Each obligation is a pair `(phi(w,z), P(w,z))`, meaning that its
case-local facts must entail `P` under the certified outer assumptions. A
certificate with outstanding `O` is conditional. A closed use must discharge
all applicable obligations, or retain an explicit assumption only where the
applicable boundary policy permits it. It cannot convert an unproved fact into
an unconditional certificate. This notation does not select an obligation
store or admit source-level propositions.

## Guarded cases and obligations

Write `case(B, phi, z, o)` for one **certified covering alternative**, not an
assertion that `phi` is feasible or that outcome `o` occurs. Its data `o` may
itself describe many concrete outcomes. `GAMMA; L, entry, phi |- P` means the
implication holds for every well-scoped world and witness satisfying those
assumptions. A locally bound witness cannot escape its case unless a separate,
valid interface binds it. Generalization and instantiation preserve kinds,
scopes, dependencies, row constraints and guards; two distinct parameters are
not assumed unequal.

The first rule weakens a case only by *adding* possibilities. `rep(o)` is the
set of concrete outcomes represented by `o` for the same world and correlated
facts. It does not license combining a value from one case with the state or
dependencies of another and then treating that tuple as exact.

```sequent
C-Case-Weaken :=
  GAMMA; L, entry |- case(B, phi, z, o)
  GAMMA; L, entry |- phi implies phi_wide
  GAMMA; L, entry, phi |- rep(o) is a subset of rep(o_wide)
  ===>
  GAMMA; L, entry |- case(B, phi_wide, z, o_wide)
```

A case may be split only if the new guards cover the old case under its
assumptions. `P` need not be decidable; an unproved branch remains a case.
The two alternatives do not assert that either branch occurs.

```sequent
C-Case-Split :=
  GAMMA; L, entry |- case(B, phi, z, o)
  GAMMA; L, entry, phi |- P or not P
  ===>
  GAMMA; L, entry |- case_pair(B, (phi and P, z, o), (phi and not P, z, o))
```

A checker with no type-level negation can retain the original unsplit case or
a conservative may-bound instead. A branch is discarded only with an
established contradiction under its guard, not because proof search failed.
Case weakening and splitting require the whole resulting collection to retain
coverage; one case is never a whole-program coverage proof.

The following rules accumulate and discharge a new composition's obligation.
`C-Require` does not prove `P`; it records the same scoped implication. The
result of `C-Discharge` can be used only with the remaining obligations and
outer assumptions intact. Duplicated obligations may be shared only when their
subjects, guards, activation and assumptions are the same.

```sequent
family guarded-obligations:
  C-Require :=
    GAMMA; L, entry |- J [O]
    phi and P are well scoped for the case witnesses z
    ===>
    GAMMA; L, entry |- J [O union {(phi, P)}]

  C-Discharge :=
    GAMMA; L, entry |- J [O union {(phi, P)}]
    GAMMA; L, entry, phi |- P
    ===>
    GAMMA; L, entry |- J [O]
```

An obligation about a normal return is vacuous when a **complete** normal
cover proves there are none. Ordinary scope, type, row, and structural
continuation-use checking remain independent of that vacuity. In particular,
`U(k, discard, available, consumed)` describes a transition; it must be
applied under an independently established incoming available state. The
[normal-return rule](first-slice-normal-return-judgments.md#candidate-entailment-rule)
checks each covered result against a continuation's assumptions without
rechecking that continuation. The [discard rule](first-slice-close-rules.md#dependencies-and-the-discard-composition)
requires every covered capture case and a shared close row.

## Finite, recursive and open contracts

A finite family of guarded alternatives can cover a fragment when its
producer establishes that each actual boundary outcome is represented and
that each request residual has the same property. `C-Union` combines already
certified component covers over the same subject and entry; its conclusion is
the union of their alternatives, with their guards and obligations retained.
It is valid only when the component alternatives jointly cover the producer's
actual behavior. Merely listing cases is not proof of that premise.

```sequent
C-Union :=
  for each i, GAMMA; L, entry |- e : A ! epsilon ; B_i [O_i] on domain D_i
  the domains D_i cover all applicable executions of e under entry
  ===>
  GAMMA; L, entry |- e : A ! epsilon ; union_i B_i [union_i O_i]
```

The producer can establish the domain partition using its own introduction
rules, such as checked match arms. A consumer applies the resulting certificate;
it does not reopen `e` to rediscover the partition. A less precise `unknown(U)`
may represent the union instead, but `U` must conservatively include all
relevant return, request and residual, non-return and failure possibilities
under its stated boundary assumptions. In particular, absence of a listed
request or dependency in `U` proves nothing unless its interface establishes
that absence. Unknown discard safety is an obligation for discard; it does
not alone reject a resource-free resume.

For recursion, let `X` be an already certified family of behavior contracts
parameterized by the declaration's admitted type, row, entry and other
boundary indices. Checking the recursive declaration and constructing its
coverage are outside this slice. The following rule consumes that established
interface at a new in-slice boundary. `sigma` is an admitted, capture-avoiding
type and row instantiation; its constraints and any remaining obligations
stay attached to the instantiated contract.

```sequent
C-Use-Recursive-Contract :=
  GAMMA; L |- opaque declaration has certified contract X [O]
  GAMMA; L |- sigma has the admitted kinds and satisfies its established constraints
  ===>
  GAMMA; L |- instantiated_contract(X, sigma) : X[sigma] [O[sigma]]
```

A broad `X` can contain an unknown request or non-return; it may be safe but
too imprecise to establish discard or dependency independence. A consumer uses
its instantiated `X`; it does not recheck the body or reconstruct a recursive
proof. A type substitution does not identify distinct runtime activations.
This schema does not extend current rank-1 polymorphism or allow unadmitted
polymorphic recursion.

A finite graph or recursive type may represent some such `X`, but this record
does not establish that all Ash behaviors have a finite representation or that
coverage and inclusion are decidable. The external producer must establish its
own finite- and infinite-execution coverage; a cycle in a certificate does not
by itself establish either. Unknown calls and unresolved `O` remain visible as
boundary obligations. No recursive producer rule or solver is selected here.

## Binding and exposed request composition

For a normal initializer return, use
[`Seq-Return` and `Seq-Remainder-Case`](first-slice-sequencing-cases.md#normal-return):
the actual result, post-state, dependencies and saved pre-binding environment
instantiate the one certified remainder. The composed case retains both the
initializer and remainder guards. The binding frame is discharged before a
request made by the remainder. Non-return does not enter it. Failure disposal
is still an explicit coverage obligation; the failure origin alone is not a
complete final-outcome case.

For an exposed request in the initializer, use
[`J-Bind-Request-Case`](first-slice-request-sequencing-judgments.md#candidate-rule-carry-a-request-through-a-binding).
It preserves the request, local control, entry activation and pending binding
frame, then composes the certified whole-initializer residual with the same
remainder for every admitted actual reply and interpreter context. The
residual compatibility premise must be derived from the original certificate
under those reply and handler conditions, or remain an obligation. It cannot
be obtained by inspecting the initializer again. If an inner handler discards
an inner capture, its clause may still make the initializer return normally;
only abandonment of the pending binding frame prevents entry through that
frame.

`perform` first saves its lexical `theta` at its own entry and then evaluates
its operand. The same case relation binds the payload and post-operand state,
while the pending request frame retains that entry's `theta` across operand
requests and residuals. Request introduction and the row union do not select a
handler or prove a request happens. See the
[perform composition](first-slice-request-sequencing-judgments.md#candidate-rule-introduce-a-request)
and the [operational steps](../../../spec/dynamic-semantics.md#effect-handlers-and-completion).

## Handler composition

Let `H` be one already checked source-handler boundary, including its exact
instance, saved lexical context and clause contracts. Its ordinary body and
clause type, scope, pattern coverage, least row and structural usage premises
are checked independently of any possibly false behavior guard. Each clause's
behavioral contract is separately **conditional**, as a projection of the
same certification, on the actual payload, fresh owner, capture and context.
A new handler composition must establish those assumptions for each covered
selection. It does not verify the body or clauses again.

The following case rules specify the normal, forwarded and selected behavior.
`Handle_H(B)` is a candidate transformation of certified contracts. Each
case is under the given `phi` and its local witnesses. `body_return` and
`body_failure` are facts about this body boundary; they do not assert that
those alternatives execute. The failure case retains the complete applicable
disposal contract rather than assuming that its reason survives disposal.

```sequent
family handler-body-outcomes:
  H-Return :=
    GAMMA; L, entry |- case(B_body, phi, z, return(v, state, deps))
    ordinary handler admission and boundary premises are established
    GAMMA; L, entry, phi |- remove_returned_handler(H, state) = state_out
    ===>
    GAMMA; L, entry |- case(Handle_H(B_body), phi, z, return(v, state_out, deps))

  H-Failure :=
    GAMMA; L, entry |- case(B_body, phi, z, failure(origin, disposal))
    ordinary handler admission and boundary premises are established
    disposal covers the applicable failure behavior through H
    ===>
    GAMMA; L, entry |- case(Handle_H(B_body), phi, z, failure(origin, disposal))

  H-Local-Divergence :=
    GAMMA; L, entry |- case(B_body, phi, z, local_divergence(locality(H)))
    ordinary handler admission and boundary premises are established
    GAMMA; L, entry, phi |- H is inside the actual pending enclosing delimiter b
    ===>
    GAMMA; L, entry |- case(Handle_H(B_body), phi, z, local_divergence(locality(b)))

  H-Unknown :=
    GAMMA; L, entry |- case(B_body, phi, z, unknown(U))
    ordinary handler admission and boundary premises are established
    GAMMA; L, entry, phi |- Top_H covers U through H and its actual enclosing control
    ===>
    GAMMA; L, entry |- case(Handle_H(B_body), phi, z, unknown(Top_H))
```

`H-Return` removes the completed handler boundary, preserves the actual value
and its other applicable facts, and does not run a source return clause.
`H-Failure` requires a disposal contract that already accounts for
this enclosing boundary; a local failure summary without that coverage cannot
satisfy it. The exact internal-failure and final-observation abstraction is
still unresolved. `H-Local-Divergence` applies only to a certified divergence
that does not select or leave `H`; an established absence of body return
alone is insufficient. The conclusion carries a locality certificate for the
actual pending outer delimiter `b`; generic nonreturn does not provide it. If
the enclosing relationship or locality is unknown, preserve a conservative
unknown case instead. A selected clause can discard the body capture and
itself return normally. Non-return does not discharge an owner or prove
termination.

`H-Unknown` supplies that fallback for a body case already represented by an
unknown bound. `Top_H` may be the universal bound for the same handler and
enclosing control, including requests selected by `H`, passed requests,
no-reply clauses, divergence, failures and their disposal. It establishes no
absence or successful return. It does not turn an otherwise uncovered body
into a certified one: the body's producer must supply either its complete
cover or a complete unknown alternative.

For each exposed body request, use the existing
[matching bounds](first-slice-matching-coverage.md#candidate-coverage-composition)
and [nearest-boundary judgments](first-slice-nearest-boundary-judgments.md#candidate-composition-rules).
A request may pass `H` only under a certified passing condition; an unknown
match must retain both possible selection and passing, or a covering unknown.
For the passing case the handler remains pending in control. `R_H` denotes the
certified residual after an admissible outside reply, with the same `H`
boundary restored around the resumed body segment. Its entry and reply facts
come from the same request case. The premise requires the actual residual
composition, not a recheck of the body.

```sequent
H-Forward :=
  GAMMA; L, entry |- case(B_body, phi, z, request(r, K, R))
  GAMMA; L, entry, phi |- the certified nearest-boundary result passes H
  GAMMA; L, entry, phi |- R_H covers each admissible restored residual of R through H
  ===>
  GAMMA; L, entry |- case(Handle_H(B_body), phi, z, request(r, K ++ H, R_H))
```

If `H` is selected, `K` and `H` move into a fresh `k` capture; `outside` stays
outside it. `P` binds the actual operation payload. The established clause
contract is instantiated under the correlated capture and context facts, and
its assumptions and resource crossings must be entailed. `Continue` records
that the clause runs under its local `CLAUSE(H,k,state)` boundary. It does not
copy clause outcomes directly to the handler result: each outcome must pass
the applicable clause-boundary rule. It is not a separate body verification.

```sequent
family handler-selection-and-clause-outcomes:
  H-Select :=
    GAMMA; L, entry |- case(B_body, phi, z, request(r, K, R))
    GAMMA; L, entry, phi |- selected_clause(r, H, P, k, C, O, bindings, clause_entry)
    C = K ++ [H] and the selection fact is for this same request case and instantiation
    GAMMA; L, entry, phi |- those same selection facts and saved_environment(H) entail the certified clause premises
    GAMMA; L, entry, phi |- clause_H(bindings, k, C, O, saved_environment(H)) has certified behavior B_clause under clause_entry
    ===>
    GAMMA; L, entry |- Continue(Handle_H(B_body), phi, (z,k,P,C,O,bindings,clause_entry), B_clause)

  H-Request-Transition-Failure :=
    GAMMA; L, entry |- case(B_body, phi, z, request(r, K, R))
    GAMMA; L, entry, phi, chi |- selection through this H or its capture preparation for the same r fails at state_fail with origin
    GAMMA; L, entry, phi, chi |- disposal_out covers this failure and its final observations from state_fail
    ===>
    GAMMA; L, entry |- case(Handle_H(B_body), phi and chi, (z,state_fail), failure(origin, disposal_out))

  H-Clause-Return :=
    GAMMA; L, entry |- Continue(Handle_H(B_body), phi, (z,k,P,C,O,bindings,clause_entry), B_clause)
    GAMMA; L, entry, phi |- case(B_clause, chi, y, return(v, state, deps))
    GAMMA; L, entry, phi, chi |- k is consumed in state and its local facts do not escape
    GAMMA; L, entry, phi, chi |- H-Pop-Clause-One removes this ungrouped physical completion and yields state_out
    ===>
    GAMMA; L, entry |- case(Handle_H(B_body), phi and chi, (z, k, P, C, O, bindings, clause_entry, y), return(v, state_out, deps))

  H-Clause-Return-Group :=
    GAMMA; L, entry |- Continue(Handle_H(B_body), phi, (z,k,P,C,O,bindings,clause_entry), B_clause)
    GAMMA; L, entry, phi |- case(B_clause, chi, y, return(v, state, deps))
    GAMMA; L, entry, phi, chi |- the certified new composition HandleGroup contains this clause and the actual adjacent logical group G with innermost k
    GAMMA; L, entry, phi, chi |- the HandleGroup delimiter is immediately outside G and its resulting outside control is O_group
    GAMMA; L, entry, phi, chi |- all logical members of G are consumed and directly forward this same return with no intervening source computation
    GAMMA; L, entry, phi, chi |- the group members and their local capture facts do not escape through v
    GAMMA; L, entry, phi, chi |- H-Pop-Clause-Group completes this actual physical group and yields state_out with control O_group
    ===>
    GAMMA; L, entry |- case(HandleGroup, phi and chi, (z,y,G,v,state,deps), return(v, state_out, deps))

  H-Clause-Request :=
    GAMMA; L, entry |- Continue(Handle_H(B_body), phi, (z,k,P,C,O,bindings,clause_entry), B_clause)
    GAMMA; L, entry, phi |- case(B_clause, chi, y, request(r, K, R))
    GAMMA; L, entry, phi, chi |- k has the correlated phase u, including its live capture contract if live
    GAMMA; L, entry, phi, chi |- R_clause covers the admissible clause residual with its owner boundary
    ===>
    GAMMA; L, entry |- case(Handle_H(B_body), phi and chi, (z, k, P, C, O, bindings, clause_entry, y, u), request(r, K ++ CLAUSE(H,k,u), R_clause))
```

`H-Request-Transition-Failure` is an alternative to successful request
processing through `H`, not a failed
clause execution. Its guard and failure state come from the applicable
primitive failure table for that exact request and transition. If the table
does not yet establish the failure phase or disposal, retain a covering
unknown; do not assume that a fresh owner or completed transfer exists.
Failure alternatives for passing or selecting other interpreter kinds remain
with their own transition contracts. This case does not claim that every
well-typed source request can reach a malformed-control failure.

A normal clause return removes its consumed local owner boundary before
passing the actual result outward. `H-Clause-Return` applies when its physical
boundary has one completion. `H-Clause-Return-Group` instead applies to the new
composition containing an actual merged group: the same return passes through
all of its adjacent logical boundaries in the one physical batch described
below. The `HandleGroup` conclusion is delimited immediately outside that
group; any pending binding, clause continuation or other context beyond it is
composed separately using its existing interface. Its premises reuse those
clause and group interfaces; they do not
recheck the corresponding clauses. No separately executable runtime state is
introduced between logical members. A clause request retains that boundary in
its current live or consumed state; if another handler captures it, its
capture obligations follow the separate ownership rules. The local `k` and
capture, payload and outside-context witnesses are scoped to the selection
and cannot escape as source values or unsupported outward facts. Removing the
consumed clause must likewise preserve only facts valid beyond that boundary.

The following rules cover additional clause alternatives. A clause failure
needs the actual local owner state and its applicable disposal behavior;
`disposal_out` covers that entire boundary response and any final observation.
`local_divergence(locality(CLAUSE(H,k)))` certifies behavior that stays
inside that actual clause boundary without selecting an enclosing handler or
abandoning the boundary. The outward locality witness names the actual
pending outer delimiter, not the captured and inactive `H`. If that witness
cannot be established, retain an unknown case.
For an unknown case, `U_clause` must be an established upper bound after
accounting for the clause boundary, its possible phases and capture ownership.
None of these premises follows merely from an ordinary type or row.

```sequent
family handler-clause-other-outcomes:
  H-Clause-Failure :=
    GAMMA; L, entry |- Continue(Handle_H(B_body), phi, (z,k,P,C,O,bindings,clause_entry), B_clause)
    GAMMA; L, entry, phi |- case(B_clause, chi, y, failure(origin, disposal))
    GAMMA; L, entry, phi, chi |- disposal_out covers failure disposal through CLAUSE(H,k) and its actual phase
    ===>
    GAMMA; L, entry |- case(Handle_H(B_body), phi and chi, (z,k,P,C,O,bindings,clause_entry,y,disposal_out), failure(origin, disposal_out))

  H-Clause-Local-Divergence :=
    GAMMA; L, entry |- Continue(Handle_H(B_body), phi, (z,k,P,C,O,bindings,clause_entry), B_clause)
    GAMMA; L, entry, phi |- case(B_clause, chi, y, local_divergence(locality(CLAUSE(H,k))))
    GAMMA; L, entry, phi, chi |- this clause boundary is inside the actual pending enclosing delimiter b
    ===>
    GAMMA; L, entry |- case(Handle_H(B_body), phi and chi, (z,k,P,C,O,bindings,clause_entry,y), local_divergence(locality(b)))

  H-Clause-Unknown :=
    GAMMA; L, entry |- Continue(Handle_H(B_body), phi, (z,k,P,C,O,bindings,clause_entry), B_clause)
    GAMMA; L, entry, phi |- case(B_clause, chi, y, unknown(U))
    GAMMA; L, entry, phi, chi |- U_clause soundly covers U through the actual clause boundary and its possible phases
    ===>
    GAMMA; L, entry |- case(Handle_H(B_body), phi and chi, (z,k,P,C,O,bindings,clause_entry,y,U_clause), unknown(U_clause))
```

If disposal or unknown-boundary coverage is not established, the respective
case remains an obligation. No rule turns it into an empty outcome. In
particular, a request from the clause can be captured by an outer handler and
then discarded; that path follows the request and owned-close rules, not the
local-divergence rule.
A request made directly by the selected clause is evaluated outside the moved
`H` boundary. It may be handled by a clause-local boundary or forwarded to
`O`; it is not silently removed by the original handler's row removal.
`H-Select` is only one possible selection. Complete handler behavior combines
all feasible selection, forwarding, cell/native/outward, normal, non-return,
failure and unknown alternatives. It preserves the assumptions and guarded
obligations of each one. The rules do not choose an interpreter merely by
naming it, and a may-selection is not an exact `nearest` proof. The fresh `k`
in this case is bound for each actual selection represented by the case; the
rule does not prove that a selection occurs or publish an owner outside that
case's scope.

## Resume, no reply and captured control

A selected clause's available owner `k` carries the actual captured segment
`C` through the selected `H` boundary. Let `Segment_C(q, state_q, deps_q)`
be the certified continuation of that segment to the selected handler
boundary after the actual reply. It is **not** the clause suffix and need not
be the whole initializer residual. `S` is the already certified continuation
of the `resume` expression inside the clause. The selected handler is
reinstalled around `Segment_C`, while `S` remains after that boundary. The
following rule describes one normal operand case; it uses the independent
ordinary and structural resume premises and the operand's normal-fit proof.

```sequent
H-Resume-Case :=
  GAMMA; L, entry |- clause owner k is structurally available and active
  GAMMA; L, entry |- ordinary(resume operand) : A ! epsilon_out
  GAMMA; L, entry |- operand : Q ! epsilon_q ; B_q
  U(k, operand, available, available)
  epsilon_q is included in epsilon_out
  GAMMA; L, entry |- case(B_q, phi, z, return(q, state_q, deps_q))
  GAMMA; L, entry, phi |- the same actual k is live and reply/restore premises hold
  GAMMA; L, entry, phi |- restored = Handle_H(Segment_C(q, state_q, deps_q))
  GAMMA; L, entry, phi |- restoration atomically places CLAUSE(H,k,consumed) outside restored
  U(k, S, consumed, consumed)
  GAMMA; L, entry, phi |- S fits each normal return of restored under that same consumed boundary
  ===>
  GAMMA; L, entry |- continue_under_case(resume_behavior(k), phi, (z,q,state_q,deps_q), Seq(restored, S))
```

The rule consumes the same owner once on successful restoration and retains
its consumed clause boundary outside the restored segment. `S` is the
already established continuation under that consumed structural state; other
state facts come from the actual restored-segment return. `continue_under_case`
is the guarded continuation relationship with its local witness tuple made
explicit. The conclusion binds the operand-case witnesses and correlated reply
and state locally; subsequent cases must preserve that scope. `Seq` enters
`S` only when the restored segment and handler boundary normally return; the
segment's result is not necessarily `q`. An operand request keeps the pending
resume frame; operand non-return or abandonment does not perform this restore.
The original prefix before the captured request is never replayed. To obtain
the behavior of a **whole initializer** with an inner `H`, compose this clause
continuation and the initializer's own surrounding context as well; do not
substitute the segment's answer for the initializer's final return. The
[dynamic resume steps](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
are the intended correspondence. The rule still requires a derivation of
`Segment_C` and its restored contract from certified capture facts.

A discard or other no-reply interpreter path has its own branch. For an
ordinary source clause, the [owned-discard rule](first-slice-close-rules.md#dependencies-and-the-discard-composition)
checks structural availability independently, covers every selected capture,
and checks the guarded close, outside completion, dependency, interpreter and
row obligations. It consumes `k`, schedules owned close and then continues the
clause; it does not apply `Segment_C` or manufacture a reply. The clause can
return normally after successful close. Other no-reply, failure or
non-returning interpreter paths enter through their established boundary
contracts. If a selected capture contains a pending binding frame, abandoning
it does not enter that binding's remainder. If the capture is inside the
initializer and leaves that binding outside, a later normal handler result can
still enter the binding. A missing no-reply branch cannot be inferred from a
reply-indexed family.

## Deriving the handler boundary operations

The following rules refine the boundary operations used above. They are
conditional on established facts and do not recheck either side of a
composition. Write `physical_control(state)` for the evaluator's actual
ordered continuation, and `control(state)` for its certified **logical**
expansion at the indicated point. They agree except where one physical
consumed clause frame represents several adjacent logical completions. The
expansion retains their ordered dynamic clause identities and the physical
frame's static handler/owner pair and count; it is a type-level correspondence,
not additional runtime frames or a required runtime identity registry. It is
established with the new composition and reused as a certificate. The
distinct logical identities and their provenance come from that certified
ghost interface; the physical count and static pair alone cannot recover
them. Each one-shot owner remains distinct. A `++` below
composes ordered logical control supplied by those interfaces. It is not a
request to traverse a certified constituent's frames.

Logical expansion length is not physical frame count. Capture quotas,
reservations, accounting and work use the actual physical lengths from their
own correlated contracts, never the number of expanded logical clauses. An
expanded intermediate boundary is not an observable or separately executable
machine state. Only the physical grouped transition yields an actual next
state; it may cover several logical boundary returns in one batch. The
equalities describe the newly formed composition and must be supplied by its
certified context interface. Owner phases and ownership can
also occur in state facts, not just in its control; `absent` removes a
completed clause-local owner from the outward state, while `consumed` records
that the owner no longer owns its former capture.

### Remove a completed boundary

At a normal handler return, `H` is the top logical boundary; at a normal
selected clause return, the top logical clause boundary records the same
consumed owner. The evaluator may combine adjacent consumed ordinary clauses
with the same static pair into one physical frame with a positive
`completion_count`. The one-clause rule applies only to an actual physical
count of one. The grouped rule covers the entire physical frame and all its
logical members at once. Neither rule infers consumption from normal-return
coverage; the independent usage and actual owner-state premises still apply.

```sequent
family completed-boundary-projection:
  H-Pop-Handler :=
    GAMMA; L, phi |- control(state) = H :: O
    GAMMA; L, phi |- removing this boundary and dropping its retained metadata yields actual state_out
    ===>
    GAMMA; L, phi |- remove_returned_handler(H, state) = state_out and control(state_out) = O

  H-Pop-Clause-One :=
    GAMMA; L, phi |- control(state) = CLAUSE(H,k,consumed) :: O
    GAMMA; L, phi |- the corresponding actual physical clause frame has completion_count = 1
    GAMMA; L, phi |- owner(state,k) = consumed
    GAMMA; L, phi |- k and its local capture facts do not escape through the result
    GAMMA; L, phi |- this physical return transition succeeds and yields actual state_out
    ===>
    GAMMA; L, phi |- H-Pop-Clause-One removes k with control(state_out) = O and owner(state_out,k) = absent

  H-Pop-Clause-Group :=
    GAMMA; L, phi |- the actual top physical ordinary clause frame has static pair key and completion_count = m, with m > 1
    GAMMA; L, phi |- the certified expansion is control(state) = [CLAUSE(H,k_1,consumed), ..., CLAUSE(H,k_m,consumed)] ++ O
    GAMMA; L, phi |- every k_i is a distinct consumed dynamic activation with static pair key, and no k_i or its capture facts escape through the result
    GAMMA; L, phi |- this physical grouped return transition succeeds and yields actual state_out
    ===>
    GAMMA; L, phi |- H-Pop-Clause-Group removes the whole group, control(state_out) = O, and each owner(state_out,k_i) = absent
```

The group expansion must be tied to that actual physical frame and its
certified dynamic activations; in `CLAUSE(H,k_i,consumed)`, `H` denotes the
shared static handler identity, while each `k_i` retains its own dynamic
selection and saved-context provenance. Identical static pairs alone do not
identify those activations. With tracing enabled, the successful grouped return reserves
for and emits `m` clause-return events in the one physical transition. It does
not perform `m` separate reservations or expose intermediate source steps.
The ordinary return loop has already popped the physical frame before its
pending-disposal check and any later validation or trace reservation. Those
failure cases retain the actual post-pop failure state; they cannot use either
successful rule or pretend that a portion of the group returned first.

The state interface must describe the actual boundary and outside control; an
ordinary result type does not supply that equality. Local capture witnesses
remain scoped after the boundary is removed. Dropping a retained environment
or other metadata may record a pending disposal failure; `state_out` carries
that actual state. Neither rule asserts that every non-control field is
unchanged or that the next disposal check succeeds. Outside owner facts and
the actual result remain available only as established by their applicable
transition and value contracts. These projections correspond to
[handler and clause return](../../../spec/dynamic-semantics.md#effect-handlers-and-completion).

### Select a source handler and form its capture

For an established request case `r`, let its actual operand be `P` and its
certified selection context be `K_all`. The exact selection judgment is the
result of the [nearest-boundary rules](first-slice-nearest-boundary-judgments.md#candidate-composition-rules),
under the same request, instantiation and condition. It identifies crossed
prefix `K` and outside `O`. The established dependency cover supplies actual
payload facts; [payload crossing](first-slice-resource-rules.md#r4-actual-result-and-payload-crossing)
checks crossed cell owners and applicable trusted recipients. Other owners
use their established boundary obligations. The operation and checked
irrefutable clause pattern determine its bindings in the handler environment.

```sequent
H-Source-Capture :=
  GAMMA; L, phi |- certified_request_case(r, P, K_all)
  GAMMA; L, phi |- request_state(r) = state_r
  GAMMA; L, phi |- selects(r, K_all, selected(H, K, O))
  GAMMA; L, phi |- payload_crossing(r, P, K, H)
  GAMMA; L, phi |- clause_of(H, operation(r)) = pattern => body
  GAMMA; L, phi |- match(heap(state_r), P, pattern) = bindings
  k is fresh for this selection activation
  C = K ++ [H]
  GAMMA; L, phi |- preparation and capture transfer for this same request and selection succeed, yielding clause_entry
  GAMMA; L, phi |- clause_entry = enter_clause(state_r, saved_environment(H), bindings, k, C, O) for that successful transition
  ===>
  GAMMA; L, phi |- selected_clause(r, H, P, k, C, O, bindings, clause_entry)
```

`enter_clause` moves `C` out of active control into the fresh live owner `k`,
sets active control to `[CLAUSE(H,k,live(C))] ++ O`, and uses the handler's
saved environment extended with the actual pattern bindings, including its
saved lexical instantiation. It preserves the heap and transfers the captured
control without copying it or discharging its obligations. Outside owner facts
are preserved or updated according to their own transition contracts: an
associated registration, for example, can change its active and pending
invocation state when the handler is selected. This slice takes that excluded
boundary's correlated update as an input; it cannot claim every outside fact
is unchanged. The
resulting `clause_entry` is part of this same selected case. The conclusion
supplies that entry, the local live owner and ordered capture to `H-Select`;
it does not prove closability or a reply. Failed preparation or transfer has
its own covered failure or unknown case; exact selection alone does not prove
that successful entry occurs. `selects` is exact under
`phi`, not membership in a may-set. If only a conservative selection cover is
known, each covered candidate must retain its condition and be checked; an
unproved candidate cannot be dropped. Source, cell, native and outward cases
remain distinct. A captured source handler is not active while its clause
runs. This is the source branch of [request selection](../../../spec/dynamic-semantics.md#effect-handlers-and-completion).

### Restore the selected segment

For a selected source clause, `C` is the same capture owned by `k`. If the
resume operand returns `q`, its pending `RESUME(H,k)` frame is followed by
the clause continuation `F ++ [CLAUSE(H,k,live(C))] ++ O`. `F` is the
pending clause control before that owner; it includes the continuation after
`resume`. This split is a fact of the new composition, not a search through a
certified body. The following rule describes the control and owner projections
of a successful restore on that one correlated case:

```sequent
H-Restore-Control :=
  GAMMA; L, phi |- C = K ++ [H] and owns(k, C)
  GAMMA; L, phi |- control(state_q) = [RESUME(H,k)] ++ F ++ [CLAUSE(H,k,live(C))] ++ O
  GAMMA; L, phi |- owner(state_q,k) = live(C)
  GAMMA; L, phi |- NearestOwner(state_q,k) for the actual resume node's static pair
  GAMMA; L, phi |- reply q and its dependencies satisfy the selected request contract
  GAMMA; L, phi |- this same restore's preparation and transfer succeed from state_q to state_restored
  GAMMA; L, phi |- the established logical expansion relates the actual physical pre- and post-restore control for these same activations
  ===>
  GAMMA; L, phi |- restore_control(k, C, state_q) = state_restored and control(state_restored) = C ++ F ++ [CLAUSE(H,k,consumed)] ++ O and owner(state_restored,k) = consumed
```

On this successful transition, the equation moves the same `C` from `k`'s ownership into active
control and changes `k`'s owner facts to consumed. It neither retains a second
owned copy of `C` nor consumes or duplicates another owner. It keeps `F` and `O` in
order; it does not execute restored frames or replay the prefix before the
request. The actual reply then enters `K`, and the handler boundary is passed
before `F` continues. Captured resource phases and completion facts are
preserved by their applicable contracts. It does not assert that work, trace,
reservation or accounting fields remain unchanged; the transition and failure
contracts describe them. A request, non-return or abandonment
while evaluating the operand does not itself apply this rule. The
[resume steps](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
specify this order.

The implementation can represent the consumed clause in that logical
equation by merging it with the immediately preceding consumed ordinary
physical clause frame. The following rule states the successful merge's
expansion, using the same capture and dynamic owner. `G_old` is the certified
logical expansion of the old physical group, not a list recovered from its
count. The runtime merge is permitted only when the old frame is adjacent,
both frames have the same static handler/owner pair and no registration or
retained association, and the increment is representable.

```sequent
H-Restore-Merged-Expansion :=
  GAMMA; L, phi |- the same live k owns C and its actual resume frame is followed immediately by its clause boundary
  GAMMA; L, phi |- the immediately enclosing physical ordinary consumed group has count m and certified logical expansion G_old
  GAMMA; L, phi |- k and every member of G_old have the same static pair but distinct dynamic identities
  GAMMA; L, phi |- both physical clause frames have no registration or retained association and m + 1 is representable
  GAMMA; L, phi |- the actual successful restore consumes k, reinstates C, and physically merges those frames into count m + 1
  ===>
  GAMMA; L, phi |- the new group's certified expansion is [CLAUSE(H,k,consumed)] ++ G_old in the same restored control
```

If the increment is not representable, the current implementation does not
merge those frames; a successful restore can retain them as two physical
frames. Other adjacency or association cases likewise require their own
established control interfaces. A failure after taking the capture remains in
the failure cover; this successful rule does not reconstruct a rolled-back
state. The [merge and restore code](../../../src/eval/machine.rs#L5153) is
implementation evidence, while the source semantics still describes adjacent
logical completion boundaries. Neither branch increases the physical capture
count by the number of logical completions.

The control equation alone cannot synthesize the *behavior* of `K` from its
ordinary types or frame identities. Let `state_restored` be the result of
`restore_control(k, C, state_q)`, with `k` already consumed. A certified
request interface must also supply a conditional delimited port
`Port(K, H, q, state_restored, deps_q) = B_inner`: behavior from the reply at
the request up to the selected `H` boundary, **before** its return transition
and before entering `F`. `Handle_H(B_inner)` supplies the segment through the
already restored boundary; it does not install a second copy of `H`. The
`Segment_C(q, state_q, deps_q)` in `H-Resume-Case` uses this port after the
restore equation establishes `state_restored`. `Port`
retains the original request case, local boundaries, reply facts and applicable
assumptions. In-slice constructors form a new port by composing their own new
frame with established constituent ports; an opaque certified segment supplies
its port as a boundary input. Applying it does not open `K` or its producer.
`H-Resume-Case` composes `Handle_H(B_inner)` with the certified `F` only after
the segment returns normally, under the consumed `k` boundary. An outside
selection's clause continuation remains outside that composed segment.

For a forwarded request, the same port discipline constructs `R_H`: the
established local segment port includes this passed `H` in its restored
control, while the selected outer interpreter's clause continuation is supplied
by that interpreter's boundary contract. The port is indexed by that same
selection, actual reply and post-reply state. If a port or fit premise is
missing, neither `R_H` nor the restored behavior is established merely by
an ordinary request row or a whole-expression residual.

### Bottom-up frame producers and case coverage

#### Enter a new expression

The entry rules connect a newly checked source construct to the frame and
boundary producers below. They consume the already certified operand, body
and clause contracts at their actual conditional entries. The producer of a
new expression establishes these entries while checking that expression; a
later user instantiates its resulting certificate. These rules do not inspect
the constituents again. Their success cases are only part of the expression's
cover: use the applicable primitive failure table and disposal contract from
the [failure judgments](first-slice-failure-judgments.md#introduce-and-compose-failure-cases)
for every failure before entry or while installing a frame. A missing table
is represented by a covering unknown-failure case, not a successful entry.

In `Enter-Strict`, the form determines both `f` and its transition: `perform`
uses `Frame-Perform`, `resume` uses `Frame-Resume`, a cell initializer uses
`Frame-Cell-Acquire`, and a binding context uses `Frame-Binding`. Source cleanup
initialization uses the binding context described below; the current Core
cleanup node does not install a cleanup-initializer frame. `start`
retains the form's actual entry environment and lexical instantiation, and
installs the new pending frame before evaluating the operand. `B_e` is the
operand's established behavior at that entry. `F_f` is the named frame
transition followed by the already certified context up to the chosen
delimiter. For `Frame-Resume`, that transition already includes its certified
clause continuation: `F_f` must not append the same continuation again.

```sequent
Enter-Strict :=
  GAMMA; L, entry |- ordinary typing, row and structural premises hold for new form n
  GAMMA; L, entry, phi |- start(n, entry) = (f, entry_e) succeeds
  GAMMA; L, entry, phi |- the certified operand contract instantiated at entry_e has behavior B_e
  GAMMA; L, entry, phi |- F_f is the named frame producer with the same f and its established following context
  GAMMA; L, entry, phi |- for each covered normal operand result, the applicable frame cases and failures or their covering unknown are supplied
  ===>
  GAMMA; L, entry |- success_case(behavior(n in context_d), phi, then_d(B_e, F_f))
```

This rule preserves a request from the operand with `f` pending; it does not
apply the frame until the operand actually returns. An operand's non-return,
failure or unknown case remains in the cover. A resume's live owner remains
live during operand evaluation. The saved `perform` instantiation is the one
from entry, even when operand evaluation makes requests. The cell and cleanup
owners do not exist until their respective successful acquisition transitions.
`success_case` means installation succeeded; it does not assert that the
operand, frame transition or enclosing expression completes.

Source cleanup resolution lowers its initializer to a preceding binding whose
binder is the cleanup callback. Its initializer can request or suspend with
that ordinary binding frame pending. Only after its actual normal result is
bound can execution reach the Core cleanup node. The elaborated path may also
include an intervening saved-allocation-context query; its certified behavior
and binding precede acquisition and must be composed when present. That query
can itself request, fail or not return. These are the source and Core
relationships shown by [cleanup lowering](../../../src/resolve.rs#L10269),
[elaboration](../../../src/elaborate.rs#L16879) and
[evaluator entry](../../../src/eval/machine.rs#L1859); they do not impose an
additional Core initializer frame.

A handler enters its body under a new boundary rather than waiting for an
operand to return. Its saved environment and lexical instantiation are from
the handler entry, and its clause contracts remain conditional on the actual
selection. The body contract is instantiated at the same entry with `H`
pending. `Handle_H` uses the handler cases above, including unknown and
transition failures; its complete cover additionally requires all applicable
selection alternatives. The enclosing context is composed once after this
handler's outcomes.

```sequent
Enter-Handler :=
  GAMMA; L, entry |- ordinary handler typing, coverage, row and structural premises hold
  GAMMA; L, entry, phi |- installing H at entry succeeds with body entry entry_H
  GAMMA; L, entry, phi |- the certified body at entry_H has behavior B_body
  GAMMA; L, entry, phi |- H carries the certified conditional clauses and saved entry context
  GAMMA; L, entry, phi |- applicable selection, transition and disposal cases are supplied or conservatively covered
  ===>
  GAMMA; L, entry |- success_case(behavior(handle body with H), phi, Handle_H(B_body))
```

The operational entry and operand order are given by
[handler, request and resume execution](../../../spec/dynamic-semantics.md#effect-handlers-and-completion),
[cell execution](../../../spec/dynamic-semantics.md#scoped-cell-execution) and
[cleanup execution](../../../spec/dynamic-semantics.md#scoped-cleanup-actions).
These rules specify how to assemble the new contract, not an additional walk
over a checked operand or a promise that the current compiler constructs it.

#### Frame transitions

The constructor rules below produce the frame and Core-node transitions used
to form `T_let`, `T_out`, `T_acquire`, `T_cell`, `T_cb`, `T_cleanup` and
`T_finish`. Their inputs are the one already certified judgment of each
operand, body, clause or action, together with the new constructor's own
identity, saved environment and boundary facts. A conditional judgment can
be instantiated at a new entry after its premises are entailed; it is never
rederived by checking the constituent. A newly introduced frame can use its
own saved data. A certified opaque frame or callable instead supplies its
established interface; these rules do not inspect it.

Write `Step(f, v, state, deps) = B` for the behavior after the newly formed
frame `f` receives the **actual** normal value `v` and associated facts. Each
rule below applies to one correlated case under its stated guard. Its result
can itself request, return, diverge, fail or be unknown. Ordinary types,
rows, kind, pattern coverage and structural usage are checked independently
of behavioral reachability. They remain required even if no normal value can
reach the frame.

For a binding, `f` saves the environment and lexical instantiation at binding
entry. Its checked irrefutable pattern and the actual runtime match supply the
bindings; the result uses the single previously certified remainder judgment.

```sequent
Frame-Binding :=
  GAMMA; L, phi |- f is the new binding frame for checked pattern p and saved environment E
  GAMMA; L, phi |- match(heap(state), v, p) = bindings
  GAMMA; L, phi |- entry_s is state with environment extend(E, bindings)
  GAMMA; L, phi |- the same v, state, deps establish the certified remainder's entry assumptions
  GAMMA; L, phi |- instantiated remainder behavior at entry_s is B_s
  ===>
  GAMMA; L, phi |- Step(f, v, state, deps) = B_s
```

`entry_s` uses the saved binding environment, not the initializer's final
lexical environment. Pattern matching is the ordinary transition on the
actual value, not a recheck of the certified remainder. `B_s` retains its
own cases, requirements and failure obligations. This is the producer used by
`Port-Bind-Cross` and [binding execution](../../../spec/dynamic-semantics.md#bindings).

For a `perform` operand, the pending request frame retains the lexical
instantiation `theta` saved **before** operand evaluation. On a covered normal
operand return and successful request preparation and formation, it introduces
the actual request with that returned payload.
The request itself has no already-selected handler and does not guarantee a
reply. Its empty local residual is the identity reply family defined below; the
enclosing constructor adds its pending frames using `Port-Bind-Cross` or the applicable rule below.

```sequent
Frame-Perform :=
  GAMMA; L, phi |- f is the new REQUEST(op, theta) frame for the certified operation contract P -> Q
  GAMMA; L, phi |- the actual returned v : P and deps satisfy the request payload premises
  GAMMA; L, phi |- r is op at instantiate(instance(op), theta) with actual payload v and deps
  GAMMA; L, phi |- request preparation and formation succeed for this same f, v, state, deps and r
  for each applicable selected protocol and actual reply case eta for r, establish the corresponding empty-local-residual identity or retain it as O_id(eta) under the same admissibility guard and witnesses
  ===>
  GAMMA; L, phi |- Step(f, v, state, deps) = request(r, [], R_id) [O_id]
```

`R_id(h,q,state_q,deps_q)` is the proposed empty-local-residual interface:
it returns the actual `q` and facts at the local delimiter with no local
pending frame, only for an admissible selection and reply. For the source
selection and restored owner specified by `Port-Empty`, that rule establishes
the corresponding identity, with any outer selected clause suffix beyond the
delimiter. It does not establish this identity for every other interpreter
protocol. Those protocols need their own general correspondence evidence or
retain an obligation universally scoped over the applicable reply cases. The
request-formation success premise does not assume a future protocol has been
selected or that a reply occurs. The symbolic request is a logical decomposition, not an
assertion that the evaluator suspends at an open boundary; the actual request
routine continues into frame search. Its phases and failures must correspond
to this interface.

The payload may need separate owner-crossing checks when a boundary is later
selected. A request, failure, divergence or abandonment before the operand's
normal return does not perform this transition; failures and unknowns during
request preparation and formation retain their own cases. For a pending `resume` frame,
the operand's normal value is instead the actual reply. Its producer consumes
the selected owner only through the [atomic restore](#restore-the-selected-segment)
rule. `C` and the reply-indexed port are established capture facts for this
same `k`, not rediscovered frames.

```sequent
Frame-Resume :=
  GAMMA; L, phi |- f is RESUME(H,k) for an active available ordinary owner
  GAMMA; L, phi |- owner(state,k) = live(C) and v : Q satisfies the actual reply premises
  GAMMA; L, phi |- restore_control(k, C, state) = state_restored
  GAMMA; L, phi |- the certified delimited port for C at v, state_restored, deps is B_inner
  GAMMA; L, phi |- the certified clause continuation F accepts each normal return of Handle_H(B_inner) under k consumed
  ===>
  GAMMA; L, phi |- Step(f, v, state, deps) = Handle_H(B_inner) then_H F
```

The actual owner remains live while the operand is evaluated, including across
any request it makes. An outer handler that captures and resumes that operand
must restore the same owner and pending `RESUME` frame before this rule can
apply. A local discard or failure does not synthesize `v`. `F` stays outside
the selected handler boundary and its structural use of `k` starts from
consumed. An owner introduced by a later request is distinct from `k`.

When a normal value reaches a newly composed source-handler boundary, the
boundary is removed before the saved outer continuation receives that same
value. This producer does not run a return clause or invent a new handler.

```sequent
Frame-Handler-Return :=
  GAMMA; L, phi |- f is the active source handler H at the actual control boundary
  GAMMA; L, phi |- H-Pop-Handler takes this same state to state_out
  ===>
  GAMMA; L, phi |- Step(f, v, state, deps) = return(v, state_out, deps)
```

The source-clause return transitions use `H-Pop-Clause-One` or
`H-Pop-Clause-Group` according to the actual physical representation; resume
uses `H-Restore-Control`. Source request capture uses
`H-Source-Capture` and `H-Select` for the same request and selection. Thus
selection is not modeled as a normal return through the handler frame.

For a new cell scope, the initializer frame precedes acquisition. Its
successful transition uses the actual initializer result and the
[acquisition judgment](first-slice-resource-rules.md#r3-and-r5-acquire-select-read-and-write),
then instantiates the single certified conditional body at that fresh activation
and post-acquisition state. The new cell boundary interprets applicable body
requests and performs its normal close only when the body returns.

```sequent
Frame-Cell-Acquire :=
  GAMMA; L, phi |- f is the new cell initializer frame with saved environment E and identity R
  GAMMA; L, phi |- the actual initializer result v, state, deps satisfies the cell acquisition premises
  GAMMA; L, phi |- successful acquisition creates fresh a with root v and post-state state_a
  GAMMA; L, phi |- the certified cell body at the correlated a, state_a has behavior B_body
  GAMMA; L, phi |- T_cell is the conditional Frame-Cell-Return transition for a composed with the certified following port
  ===>
  GAMMA; L, phi |- Step(f, v, state, deps) = fresh_case(a, InterpretCell_a(B_body) then_cell(a) T_cell)
```

`fresh_case(a, B)` binds `a` inside each successful acquisition execution.
The conditional body, interpreted requests and completion transition use that
same case-local activation; a different execution receives its own fresh
activation even at the same source site. The witness is hidden at scope exit
and exported only through a valid scoped interface after the required
crossing and owner-discharge facts hold. It is not a free constant determined
by the pre-acquisition entry state.

Preparation failure is a distinct failure case **before** publishing `a`;
it cannot enter the body or acquire a completion obligation. Successful
acquisition binds the handle, rigid identity and sealed provider under the
saved environment, as specified by [cell execution](../../../spec/dynamic-semantics.md#scoped-cell-execution).
The cell interpretation and its covering cases are constructed below. The
following port comes from the already established outer constituent, composed
one frame at a time as described below; it is not reconstructed from a
whole-expression result.

The normal return transition for the acquired cell consumes its one completion
obligation only after the actual result crosses that owner. The root in `state`
is the root at this return, which may differ from the initializer or an earlier
snapshot. The result and dependencies passed outward are the body's actual
result; the cell's payload is not substituted for it.

```sequent
Frame-Cell-Return :=
  GAMMA; L, phi |- f is the live boundary of the same activation a in state
  GAMMA; L, phi |- result_crossing(v,a) is admitted using the actual deps
  GAMMA; L, phi |- successful release removes f and discharges a once as state_out
  ===>
  GAMMA; L, phi |- Step(f, v, state, deps) = return(v, state_out, deps)
```

This is the successful transition, not a claim that release or disposal
cannot fail. Other dependency domains and outside completion facts remain
subject to their established obligations. A captured cell moves with its owner;
resumption does not perform this normal return until the body actually reaches
its cell boundary.

Cleanup establishes a callable and one invocation owner, not a cell owner.
At the current Core cleanup node, the initializer has already returned and
its result has been bound. The Core node names that callback binder, the body,
and the action application or its saved-allocation forwarding adapter. The
evaluator looks up the bound callback and performs acquisition directly; it
does not receive the initializer value through a cleanup-specific frame.

`B_action(entry)` below is the certified behavior of the actual Core action,
including its invocation of that callback and any applicable adapter, under
the actual later invocation state and context. Its certificate supplies
requests, dependencies and assumptions. The source-to-Core correspondence
must establish that the callback binder names the actual result of the source
initializer, and that the Core action invokes that same callback with `Unit`
under the selected allocation context. If an intervening allocation query is
present, its normal result must supply that context. Those are established
lowering and entry facts or retained obligations; ordinary function checking
is not performed here.

```sequent
Core-Cleanup-Acquire :=
  GAMMA; L, phi |- n is the Core cleanup node with callback binder cb, body and certified action
  GAMMA; L, phi |- environment(state).lookup(cb) = v and v has the established callback contract and deps
  GAMMA; L, phi |- cb is bound to the certified preceding initializer result, or has an established Core-entry contract
  GAMMA; L, phi |- the action and any saved-allocation context correspond to this same callback and entry
  GAMMA; L, phi |- successful preparation creates fresh armed owner o with the Core action and environment containing cb = v in state_o
  GAMMA; L, phi |- the certified body at the correlated o, state_o has behavior B_body
  GAMMA; L, phi |- the certified Core action supplies B_action(entry) for admissible actual invocation entries
  ===>
  GAMMA; L, phi |- success_case(core_behavior(n, state), phi, fresh_case(o, B_body then_cleanup(o, B_action)))
```

Here `fresh_case(o, B)` binds the newly armed owner per successful execution.
The body, invocation and finish refer to that same case-local owner; no other
execution or failed preparation acquires it. Scope exit hides the owner after
its completion and crossing obligations are satisfied. This generative witness
cannot be promoted across cases merely because the source location is shared.

Before successful preparation no invocation owner exists. A preparation
failure retains its own internal-failure and disposal case and cannot be
presented as a successful acquisition. The source initializer is evaluated once; copying
its callable does not create another owner. The successful behavior above
uses the [cleanup scope and phase rules](first-slice-close-rules.md#introduce-and-complete-one-cleanup-owner).

When the body of that scope returns, start the armed action once and retain
the actual body result. A request inside the action keeps the running owner
and unfinished completion; after the action returns `Unit`, finish that owner
before continuing with the saved result. The alternate owned-close path saves
a close continuation instead of inventing a body result.

```sequent
family cleanup-frame-producers:
  Frame-Cleanup-Start :=
    GAMMA; L, phi |- f is cleanup owner o armed with actual action and selected allocation context
    GAMMA; L, phi |- start_action(state, o, saved(v,deps)) = state_running
    GAMMA; L, phi |- the established action invocation from state_running has behavior B_action
    ===>
    GAMMA; L, phi |- Step(f, v, state, deps) = B_action then_finish(o, saved(v,deps))

  Frame-Cleanup-Finish :=
    GAMMA; L, phi |- f is running cleanup owner o with saved(v,deps_saved)
    GAMMA; L, phi |- the actual action result is () and finish_owner(o,state) = state_out
    GAMMA; L, phi |- the certified action and finish transitions preserve v and establish deps_saved as a sound dependency cover for v at state_out
    ===>
    GAMMA; L, phi |- Step(f, (), state, deps_unit) = return(v, state_out, deps_saved)

  Frame-Close-Finish :=
    GAMMA; L, phi |- f is running cleanup owner o with saved close continuation CloseRest
    GAMMA; L, phi |- the actual action result is () and finish_owner(o,state) = state_out
    GAMMA; L, phi |- the established CloseRest behavior from state_out is B_rest
    ===>
    GAMMA; L, phi |- Step(f, (), state, deps_unit) = B_rest
```

`then_cleanup` applies `Frame-Cleanup-Start` on each actual body return;
`then_finish` applies the matching finish transition only on the actual
action return. Both use the port-frame case rules below for requests and all
other outcomes. The invocation entry includes the actual running state and
the saved selected allocation context; acquisition does not guess a future
state. The start and finish transitions preserve all other owners and applicable
outside facts, and move rather than duplicate the particular owner. Starting
is not finishing, and `Unit` is not the saved body value. An action-local
discard is admissible only if the running owner and unfinished close remain
outside the abandoned capture and can still complete. Terminal internal
failure does not promise to finish the action or run the remaining close plan.

The following case rules lift an already certified pre-frame behavior `P`
through one newly introduced frame `f` and a certified following port. They
define the coverage needed by `then_d`; `P`, its residuals and the following
port are inputs, not traversals to reconstruct their producer. `cover(P)` is
the producer's established complete case cover under the same entry. `F` maps each actual frame-entry case to the behavior produced by its
applicable `Frame-*` rule followed by the established following port up to
delimiter `d`. This composition uses the very same case and its post-frame
state; a return into the following port is subject to its own normal-entry
conditions. `G` is the
pending outer control between `f` and `d` in this composition.

```sequent
family port-frame-case-producers:
  Port-Frame-Return :=
    GAMMA; L, entry |- case(P, phi, z, return(v, state, deps))
    GAMMA; L, entry, phi |- Step(f, v, state, deps) = B_frame
    GAMMA; L, entry, phi |- F(v,state,deps) is B_frame composed with the established following port on matching normal cases
    ===>
    GAMMA; L, entry |- continue_under_case(then_d(P,F), phi, (z,v,state,deps), F(v,state,deps))

  Port-Frame-Transition-Failure :=
    GAMMA; L, entry |- case(P, phi, z, return(v, state, deps))
    GAMMA; L, entry, phi |- actual entry of f on (v,state,deps) has guarded failure eta at state_fail with origin
    GAMMA; L, entry, phi, eta |- disposal_f covers disposal and final reports from that same state_fail with pending f and G
    ===>
    GAMMA; L, entry |- case(then_d(P,F), phi and eta, (z,v,state,deps,state_fail), failure(origin, disposal_f))

  Port-Frame-Transition-Unknown :=
    GAMMA; L, entry |- case(P, phi, z, return(v, state, deps))
    GAMMA; L, entry, phi |- U_frame covers unestablished outcomes of entering this same f on (v,state,deps), including failure and disposal
    ===>
    GAMMA; L, entry |- case(then_d(P,F), phi, (z,v,state,deps), unknown(U_frame))

  Port-Frame-Entered-Case :=
    GAMMA; L, entry |- continue_under_case(then_d(P,F), phi, z, F)
    GAMMA; L, entry, phi |- case(F, chi, y, outcome)
    ===>
    GAMMA; L, entry |- case(then_d(P,F), phi and chi, (z,y), outcome)

  Port-Frame-Request :=
    GAMMA; L, entry |- case(P, phi, z, request(r, K, R))
    GAMMA; L, entry, phi |- f and G are the same pending frames for this case
    GAMMA; L, entry, phi and chi |- r exactly passes each intervening interpreter in f and G up to delimiter d
    for each admissible selection h at or beyond d and actual reply q, state_q, deps_q,
      the certified R(h,q,state_q,deps_q) covers the rest of P up to f
      its covered normal cases satisfy F's entry assumptions and the same f, G and d remain scoped
    ===>
    GAMMA; L, entry |- case(then_d(P,F), phi and chi, z, request(r, K ++ [f] ++ G, (h,q,state_q,deps_q) -> then_d(R(h,q,state_q,deps_q),F)))
```

`then_d(P,F)` is indexed by this particular saved `f` and `G`; recursive
occurrences retain them, their environments and the same delimiter. At the
outermost delimiter the following port is `Port-Empty`; otherwise it is built
by applying these same frame rules to the immediately enclosing new
constructor and its already certified constituent ports. This is an
induction on newly composed constructors, not a walk through an already
certified capture. A certified opaque port is reused as-is.

An entered frame can fail even when `P` has returned normally. The
`Port-Frame-Transition-Failure` guard and `state_fail` come from the actual
frame transition, including its pre-publication or post-publication phase;
its disposal cover includes later failures and possible final reports in the
actual pending context. In particular, failed cell or cleanup acquisition
before publication creates no owner; failure after a committed transition
must retain that transition's established state. `Port-Frame-Failure` below
is separate: it covers failures already in `P`. If the entered frame's
transition alternatives or disposal are not established, `U_frame` can be
the universal may-cover for that same entry, frame and outer control. Such an
unknown includes failure, non-return and all possible final observations; it
does not prove any success or no-error premise. For a successful frame step,
the normal entered cases remain guarded by that successful transition.

The request rule exposes only the guarded exact-pass alternative; it does
not assert a later selection or a reply. Each nearer source handler or cell
selection is covered separately by its own selected-interpreter case. A
may-match is split into its feasible guarded pass and select alternatives;
an unestablished alternative stays unknown, never silently passes. The
coverage premise includes all of these alternatives. `R` is delimited at `f` and includes any selected *inner* handler's
post-resume clause work needed to reach `f`. The nearest-boundary rule
separately decides whether `f` is captured or remains outside. An outer
handler's clause suffix is not appended inside its own capture. If the
certified residual does not supply the required delimited relationship, the
premise remains an obligation; a whole-expression result is not a substitute.

`local_divergence(locality(b))` carries a scoped certificate that this
particular divergence remains inside boundary `b`: it never reaches or
abandons it and never selects outside it. A producer may attach that witness
to an established local-divergence case only when those properties are
established under the same guard and witnesses. The frame rule lifts the
certificate from `f` to its enclosing delimiter `d`; the cell rule preserves
the cell-delimiter certificate. An enclosing frame can use that scoped fact
again. Generic `nonreturn`, an unqualified divergence, or a shared source site
alone does not prove locality. If the required locality cannot be established,
use the appropriate unknown top rather than applying this lift.

```sequent
family port-frame-nonreturn-cases:
  Port-Frame-Local-Divergence :=
    GAMMA; L, entry |- case(P, phi, z, local_divergence(locality(f)))
    GAMMA; L, entry, phi |- f and G remain pending up to d for this same divergence
    ===>
    GAMMA; L, entry |- case(then_d(P,F), phi, z, local_divergence(locality(d)))

  Port-Frame-Failure :=
    GAMMA; L, entry |- case(P, phi, z, failure(origin, disposal))
    GAMMA; L, entry, phi |- disposal_f covers this failure through the actual pending f and G
    ===>
    GAMMA; L, entry |- case(then_d(P,F), phi, (z,disposal_f), failure(origin, disposal_f))

  Port-Frame-Unknown :=
    GAMMA; L, entry |- case(P, phi, z, unknown(U))
    GAMMA; L, entry, phi |- Top_d covers every outcome of U composed with the pending f and G
    ===>
    GAMMA; L, entry |- case(then_d(P,F), phi, (z,Top_d), unknown(Top_d))
```

`Top_d` can be the universal may-cover of all outcomes within the actual
delimiter and pending control, including arbitrary replies, non-return,
disposal and final reports. Its coverage is by definition, so it requires no
proof about the unknown constituent beyond its actual entry and scope; it does not prove a
request, return or failure absent. A no-reply selection follows the selected
handler or interpreter case: it may abandon `f`, or an inner clause may return
before `f` and permit it to run. The failure rule does not claim that
`disposal_f` preserves the original failure as the final host report. The universal disposal bound is also available, covering all permitted
outcomes for the actual origin and pending frames. Such a bound retains an
explicit no-error obligation; it cannot justify a closed no-error admission. The
[agreed admission rule](first-slice-failure-judgments.md#agreed-admission-rule-for-the-first-slice)
requires proving each applicable internal-failure guard impossible or keeping
the permitted boundary obligation visible. It does not turn failure into a
normal source result or assume capacity and allocation always succeed.

For a whole port, the constructor combines these **already derived** cases
with `C-Union` only when the constituent's cover and all frame-introduced
alternatives cover the applicable executions. For every covered normal input
to a frame, that cover must include all its successful transitions and all
new transition failures and disposal outcomes, or the universal fallback;
a cover of failures already present in the constituent is insufficient. May-selection, unknown reply,
preflight failure, disposal and non-return cannot be dropped to make the
coverage premise true. This is symbolic composition, not a separate pass over
each concrete execution or a new verification of the constituent.

### Constructor-specific delimited ports

These rules construct a port for a **new** in-slice composition from its
constituents' already certified ports and conditional behaviors. They do not
inspect a certified frame list or derive a function body. Let
`Port_r(K, d, k, q, state, deps) = B` mean the established behavior beginning
with actual reply `q` at request case `r`, following the already restored
segment `K` up to but not executing delimiter `d`. The same selected capture
owner `k` is consumed in `state`; the case guard retains the original request,
activation, saved lexical instantiation and reply facts. The delimiter is a
symbolic boundary of this composition, not necessarily a source handler: an
intermediate binding, cell or cleanup frame may serve as a local delimiter.
When `d` is the selected handler `H`, this is the `Port(K,H,...)` above.
`Port` does not cover execution of the selected clause suffix beyond `H`.

Write `P then_d T` for case composition at a **new** boundary. It is defined
by the following use of the already established sequencing and handler rules,
not by rerunning either constituent:

- For each covered normal return of `P`, instantiate the one certified
  conditional continuation `T` with that same actual value, state and
  dependencies, after the named frame transition. Its guard is conjoined with
  the return guard. The transition must establish `T`'s premises.
- For a request before that transition, retain its actual payload, guarded
  residual, pending frame and `d`; apply the same case composition after an
  admissible reply. An independently selected inner handler can instead
  discard its own capture and return through its own clause. Whether it owns
  the pending frame is established by boundary selection, not by the row.
- A covered local non-return does not execute the transition. Failure carries
  the applicable boundary-aware disposal contract. Unknown behavior remains a
  covering unknown or an obligation. None proves normal return.

The [binding cases](first-slice-sequencing-cases.md#normal-return),
[request sequencing](first-slice-request-sequencing-judgments.md#candidate-rule-carry-a-request-through-a-binding)
and [handler outcomes](#handler-composition) provide these case eliminations;
`normal_fits` supplies each normal-return compatibility proof. A missing
transition, residual or coverage fact is not filled in by `then_d`. In the
rules below, an equality of port expressions describes a conditional
behavioral contract, not a compile-time assertion that the corresponding case
executes. Every fresh symbolic result and state is scoped to its own case.

For the empty segment, the actual reply reaches the delimiter unchanged. It
does not yet run the delimiter or the selected clause continuation.

```sequent
Port-Empty :=
  GAMMA; L, phi |- control(state) begins with delimiter d
  GAMMA; L, phi |- selected_owner(k) is consumed and q, state, deps are the actual reply facts
  ===>
  GAMMA; L, phi |- Port_r([], d, k, q, state, deps) = return_at(d, q, state, deps)
```

Here `exact_selected_capture(r,k,C)` in the rules below is the projection of
the same `selected_clause(r,H,p,k,C,O,bindings,clause_entry)` established by
`H-Source-Capture`. It retains the request condition, lexical instantiation,
selected boundary and activation; membership in a may-selection set alone
cannot establish it. `k` is not a new owner introduced by a port rule.

For a monomorphic binding, let `f` retain the binding's preceding environment,
its one certified remainder and the binding-entry facts. `K_e` is the
initializer's segment to `f`; `K_out` continues from the remainder to the
selected handler `H`. The selected `k` and `H` are the same throughout this
case. `T_let` uses the actual initializer result to bind `x` in `f`'s saved
environment and starts the certified remainder, with `K_out` and `H` still
pending. Its behavior is conditional on that result's state and dependencies.

```sequent
Port-Bind-Cross :=
  GAMMA; L, phi |- exact_selected_capture(r, k, K_e ++ [f] ++ K_out ++ [H])
  GAMMA; L, phi |- Port_r(K_e, f, k, q, state, deps) = P_e
  GAMMA; L, phi |- T_let is the certified binding transition and remainder through K_out to H
  GAMMA; L, phi |- each covered normal result of P_e satisfies T_let's assumptions
  ===>
  GAMMA; L, phi |- Port_r(K_e ++ [f] ++ K_out, H, k, q, state, deps) = P_e then_H T_let
```

If the selected handler is *inside* the initializer, `f` lies outside its
capture. The initializer's port to that handler is unchanged; it is not
composed with the binding inside the capture. After an inner clause eventually
returns a whole initializer result, the separate binding rule may enter `f`.
No-reply discard of an inner capture can therefore still lead to that return.

When an operation occurs while evaluating a `perform` operand, the request
frame for the *outer* `perform` is pending. Its lexical instantiation was saved
when that outer expression was entered. If the inner request is resumed, its
reply first continues the operand. Only an actual normal operand result can
introduce the outer request, with that result as payload. `T_perform` uses
`Frame-Perform`, then the established interpretation and outer port through
`K_out` up to `H`. It covers selection and failure of the newly introduced
request under its own conditions; the original inner selection does not select
an interpreter for that later request.

```sequent
Port-Perform-Operand :=
  GAMMA; L, phi |- f is the pending REQUEST(op, theta) frame saved at perform entry
  GAMMA; L, phi |- exact_selected_capture(r, k, K_e ++ [f] ++ K_out ++ [H])
  GAMMA; L, phi |- Port_r(K_e, f, k, q, state, deps) = P_e
  GAMMA; L, phi |- T_perform is the certified perform transition and outer port to H for this f and K_out
  GAMMA; L, phi |- each covered normal result of P_e satisfies T_perform's assumptions
  ===>
  GAMMA; L, phi |- Port_r(K_e ++ [f] ++ K_out, H, k, q, state, deps) = P_e then_H T_perform
```

When `K_out` is empty, the following producer supplies the formerly
conditional `T_perform` directly. The new request reaches `H` with no
intervening captured frame in this port. `P_e` is the already certified port
up to `f`, including its residuals. For each of its normal cases, let
`Req_f(v,s,D)` be the conditional behavior of entering this very `f` with
that case's value, state and dependencies. It has the following alternatives,
with their actual guards and witnesses:

| Frame-entry alternative | Result in `Req_f(v,s,D)` |
| --- | --- |
| Request formation succeeds. | `request(r_new, [], R_id)` with `Frame-Perform`'s applicable guarded `O_id`, where `r_new` uses `f`'s saved `theta`, actual payload `v` and dependencies `D`. |
| A frame-entry or request-formation phase fails. | The actual origin, failure state and the disposal/final-observation cover for that phase with the actual pending boundary. |
| A phase's applicable alternatives are not established. | A covering unknown for that same phase, state and pending boundary. |

The first alternative is `Frame-Perform`; the other alternatives use the
applicable [failure cases](first-slice-failure-judgments.md#introduce-and-compose-failure-cases).
The alternatives must cover all phases of the actual frame entry, including
disposal and instantiation. Their guards need not be disjoint, but retain the
correlation to this `v`, `s` and `D`.

```sequent
Port-Perform-Adjacent :=
  GAMMA; L, phi |- exact_selected_capture(r,k,K_e ++ [f,H]) and f = REQUEST(op,theta)
  GAMMA; L, phi |- Port_r(K_e,f,k,q,state,deps) = P_e with its certified complete cover and reply residuals
  for each covered normal case of P_e, Req_f for that same value, state and dependencies has the complete guarded alternatives above
  each request, failure, local divergence and unknown case of P_e has its applicable port-frame transition and boundary-aware disposal cover or covering unknown
  the same requirements hold for each admissible reply residual; potentially unbounded request/reply behavior has guarded coverage
  O_port carries the inherited and newly introduced obligations, including each applicable O_id, under their original guards and universally binds each local case and reply witness when its case scope is exited
  ===>
  GAMMA; L, phi |- Port_r(K_e ++ [f],H,k,q,state,deps) = P_e then_H Req_f with a complete conditional cover [O_port]
```

`Port-Frame-Return` introduces `Req_f` only after an actual operand return.
`Port-Frame-Request` instead keeps `f` pending on a request arising earlier
in the operand; its reply continues the same certified residual and this same
composition. The other port-frame rules retain the corresponding failure,
local-divergence and unknown cases. `C-Union` combines those cases under their
own guards; guarded coverage is needed if the reply chain is unbounded. None
of this selects an interpreter for `r_new`: `H` is the delimiter, and its
handling or passing is a separate composition. The successful immediate
request has an empty *local* residual; it does not claim that an enclosing
handler's continuation is empty. The formation alternatives and any
unavailable residual cover remain explicit obligations rather than a reason
to reopen `P_e` or its certified constituents.

Likewise, a request during a `resume` operand leaves the original resume frame
and its owner pending. Let `j` be that original owner and `k` the distinct
owner of the selected inner request `r`. The owner `j` may move in the new
capture or remain outside it, depending on the actual boundary positions. Its
restored live state follows the corresponding owner interface; the source site
alone does not decide it. After an actual operand result `v`, `T_resume` uses
`Frame-Resume` to consume `j` and restore *its* captured segment, then follows
the certified clause continuation only up to `H`. In particular, if `H` lies
inside that continuation, work beyond `H` is not put into this port. The reply
`q` to `r` and the later operand result `v` need not be equal.

```sequent
Port-Resume-Operand :=
  GAMMA; L, phi |- f is the pending RESUME(H_j,j) frame for the same live original owner j
  GAMMA; L, phi |- exact_selected_capture(r, k, K_e ++ [f] ++ K_out ++ [H]) and j differs from k
  GAMMA; L, phi |- the restored state preserves j's actual live ownership at its actual position
  GAMMA; L, phi |- Port_r(K_e, f, k, q, state, deps) = P_e
  GAMMA; L, phi |- T_resume is the certified restore of j and bounded clause continuation through K_out up to H
  GAMMA; L, phi |- each covered normal result of P_e satisfies T_resume's reply, ownership and continuation assumptions
  ===>
  GAMMA; L, phi |- Port_r(K_e ++ [f] ++ K_out, H, k, q, state, deps) = P_e then_H T_resume
```

These are two new frame compositions, not a traversal of `K_e`, `K_out`, the
original capture of `j`, or a checked clause. Failure and non-return before
the operand's normal result do not emit the outer request or consume `j`.
If the needed bounded continuation or ownership fact is unavailable, retain
the scoped obligation or a covering unknown; a whole-clause residual cannot
be substituted for the port up to `H`.

For a passed inner source handler `H_inner`, `K_e` ends at that boundary and
`K_out` continues to the actually selected outer handler `H`. The passing
condition concerns this request under the saved instantiations; the restored
inner handler still interprets any later matching request in the resumed
segment. `T_out` is the certified continuation from the inner handler's actual
normal result through `K_out` to `H`.

```sequent
Port-Passed-Handler :=
  GAMMA; L, phi |- exact_selected_capture(r, k, K_e ++ [H_inner] ++ K_out ++ [H])
  GAMMA; L, phi |- passes(r, H_inner)
  GAMMA; L, phi |- Port_r(K_e, H_inner, k, q, state, deps) = P_e
  GAMMA; L, phi |- H_inner and T_out have established conditional behavior contracts
  GAMMA; L, phi |- each covered normal result of Handle_H_inner(P_e) satisfies T_out's assumptions
  ===>
  GAMMA; L, phi |- Port_r(K_e ++ [H_inner] ++ K_out, H, k, q, state, deps) = Handle_H_inner(P_e) then_H T_out
```

`Handle_H_inner` uses the already restored boundary, not a second copy. If
`H_inner` is selected instead, it is the delimiter and remains outside `K_e`;
`K_out` is outside that capture. A may-match is not an exact pass. Any later
request can introduce a distinct fresh clause owner `k_next`; it must not be
identified with the consumed `k`.

When the two source handlers are adjacent in the captured control, there is
no further frame or constituent between the returned inner handler and the
outer delimiter. This supplies `T_out` in that particular case. Let
`At_H(v,s,D) = return_at(H,v,s,D)` when the actual returned control begins at
`H`. It is a delimiter result, not an execution of `H`.

```sequent
Port-Passed-Handler-Adjacent :=
  GAMMA; L, phi |- exact_selected_capture(r,k,K_e ++ [H_inner,H]) and passes(r,H_inner)
  GAMMA; L, phi |- Port_r(K_e,H_inner,k,q,state,deps) = P_e with its certified complete cover and reply residuals
  GAMMA; L, phi |- H_inner has its established admission, clause and conditional behavior contracts at this restored boundary
  GAMMA; L, phi |- the handler outcome and selection rules give Handle_H_inner(P_e) a complete guarded cover up to H, including boundary-transition failures and disposal or a covering unknown
  for each covered normal return of Handle_H_inner(P_e), the actual returned control begins at H and its value, resulting state and dependencies admit At_H
  ===>
  GAMMA; L, phi |- Port_r(K_e ++ [H_inner],H,k,q,state,deps) = Handle_H_inner(P_e) then_H At_H with a complete conditional cover
```

On a normal body return, `H-Return` and the successful boundary transition
remove `H_inner` and carry that actual value and dependencies to `H`; no
handler return clause is invoked. The post-transition state, including any
pending disposal information, is the one passed to `At_H`. An ordinary
unassociated source boundary has neither registration nor retained association;
if an associated boundary is present, its established return transition and
failures are separate inputs rather than consequences of adjacency. The
evaluator's [handler return](../../../src/eval/machine.rs#L3519) and
`E-Handle-Return` describe the corresponding successful step.

Adjacency does not mean that every later request passes `H_inner`. A request
in the resumed segment can select it and run an already certified clause, or
pass it under its own exact condition. `H-Select`, `H-Forward` and their
failure, no-reply, divergence and unknown cases supply those alternatives;
their residuals must reach this same delimiter, with guarded coverage for an
unbounded reply chain. The handler's clause runs outside its selected
`H_inner` but still inside the pending `H`. If a clause or its residual lacks
the required delimited contract, retain that obligation or a covering
unknown. The original selected owner `k` remains distinct from any fresh
owner introduced by a later selection. No body, clause or captured segment
is verified again.

For a resource initializer, `init_frame` precedes acquisition and saves the
preceding environment. `T_acquire` is the established conditional acquisition
and body contract: a normal initializer value can, after successful
preparation, create one fresh activation with its actual root and enter the
certified body. It also covers applicable preparation failure without
publishing an owner. The subsequent resource boundary, normal close and outer
continuation are part of that contract; it does not treat an initializer
request as evidence that acquisition succeeded.

```sequent
Port-Resource-Initializer :=
  GAMMA; L, phi |- exact_selected_capture(r, k, K_i ++ [init_frame] ++ K_out ++ [H])
  GAMMA; L, phi |- Port_r(K_i, init_frame, k, q, state, deps) = P_i
  GAMMA; L, phi |- T_acquire is certified for this resource, saved environment and outer port to H
  GAMMA; L, phi |- each covered normal result of P_i satisfies T_acquire's assumptions
  ===>
  GAMMA; L, phi |- Port_r(K_i ++ [init_frame] ++ K_out, H, k, q, state, deps) = P_i then_H T_acquire
```

For a request in an already acquired cell body, `cell(a)` is the **same** live
activation and owned completion at capture. If the selected outer handler
crosses that boundary, the resumed body executes with that owner restored.
`InterpretCell_a(P_b)` uses the established exact cell boundary contract to
interpret later requests that select this cell while it remains live. It
preserves source-handler precedence, actual targets and root updates, and
passes other requests outward with the cell boundary pending. It stops before
normal cell release; `T_cell` performs that transition once.
`T_cell` checks the actual body result's crossing, performs the applicable
normal release on successful completion, and continues through `K_out`; it
uses the body's resulting state, including any writes, rather than assuming
the captured root remains the final root.

The following cell contract instances expose the actual replies used by that
interpretation. Their cases and names are evidence for this particular
implementation and its declared operations, applied through the common
resource and proposition judgments; they do not prescribe cell-specific
typing rules or a dedicated verifier. `h_cell` identifies this selected builtin boundary and its
lexical activation. `R` is the certified residual of the same **delimited
port** request case; it ends at the cell boundary and does not include an
outer clause continuation.
`ContinueCell` retains its guard and local witnesses while applying the
already certified residual; it does not reopen that residual's producer.
Resource dependencies and selection are independently established for the
same case by the [cell access rules](first-slice-resource-rules.md#r3-and-r5-acquire-select-read-and-write).

```sequent
family cell-port-interpretation:
  Cell-Port-Read :=
    GAMMA; L, phi |- case(P_b, chi, z, request(r, K, R))
    GAMMA; L, phi, chi |- resource_state_of(request_state(r)) = sigma for this same request case
    GAMMA; L, phi, chi |- the nearest selected boundary is h_cell for read of activation a
    GAMMA; L, phi, chi |- read_case(r, sigma) yields reply(v, D), sigma_after
    GAMMA; L, phi, chi |- cell_reply_transition(request_state(r), h_cell, sigma_after) = state_after
    GAMMA; L, phi, chi |- resource_state_of(state_after) = sigma_after
    GAMMA; L, phi, chi |- reply_facts contains the same root's D and the separately established backing, outside dependency and state facts
    GAMMA; L, phi, chi |- R(h_cell, v, state_after, reply_facts) is the certified matching residual
    ===>
    GAMMA; L, phi |- ContinueCell(InterpretCell_a(P_b), chi, (z,sigma,v,D,sigma_after,state_after,reply_facts), InterpretCell_a(R(h_cell,v,state_after,reply_facts)))

  Cell-Port-Write :=
    GAMMA; L, phi |- case(P_b, chi, z, request(r, K, R))
    GAMMA; L, phi, chi |- resource_state_of(request_state(r)) = sigma for this same request case
    GAMMA; L, phi, chi |- the nearest selected boundary is h_cell for write of activation a
    GAMMA; L, phi, chi |- write_case(r, v, sigma) yields reply(()), sigma_after
    GAMMA; L, phi, chi |- cell_reply_transition(request_state(r), h_cell, sigma_after) = state_after
    GAMMA; L, phi, chi |- resource_state_of(state_after) = sigma_after
    GAMMA; L, phi, chi |- unit_reply_facts preserves the separately established outside dependency and state facts
    GAMMA; L, phi, chi |- R(h_cell, (), state_after, unit_reply_facts) is the certified matching residual
    ===>
    GAMMA; L, phi |- ContinueCell(InterpretCell_a(P_b), chi, (z,sigma,v,sigma_after,state_after,unit_reply_facts), InterpretCell_a(R(h_cell,(),state_after,unit_reply_facts)))

  Cell-Port-Transition-Failure :=
    GAMMA; L, phi |- case(P_b, chi, z, request(r, K, R))
    GAMMA; L, phi, chi |- state_req = request_state(r) and resource_state_of(state_req) = sigma
    GAMMA; L, phi, chi |- the actual cell selection, authentication or reply/replacement preparation for r fails under eta at state_fail with origin
    GAMMA; L, phi, chi, eta |- root(sigma,a) = old and root(resource_state_of(state_fail),a) = old
    GAMMA; L, phi, chi, eta |- disposal_fail covers disposal and final reports from state_fail in its actual boundary and owner context
    ===>
    GAMMA; L, phi |- case(InterpretCell_a(P_b), chi and eta, (z,r,state_req,sigma,state_fail), failure(origin, disposal_fail))

  Cell-Port-Write-Disposal-Failure :=
    GAMMA; L, phi |- case(P_b, chi, z, request(r, K, R))
    GAMMA; L, phi, chi |- state_req = request_state(r) and resource_state_of(state_req) = sigma
    GAMMA; L, phi, chi |- the same write selects a, authenticates its actual handle and replacement v, and preparation succeeds
    GAMMA; L, phi, chi |- the write commits replacement v for a in state_commit
    GAMMA; L, phi, chi, eta |- disposal after that commit fails at state_fail with origin
    GAMMA; L, phi, chi, eta |- disposal_fail covers remaining disposal and final reports from that state_fail in its actual boundary and owner context
    ===>
    GAMMA; L, phi |- case(InterpretCell_a(P_b), chi and eta, (z,r,state_req,sigma,v,state_commit,state_fail), failure(origin, disposal_fail))

  Cell-Port-Transition-Unknown :=
    GAMMA; L, phi |- case(P_b, chi, z, request(r, K, R))
    GAMMA; L, phi, chi |- state_req = request_state(r)
    GAMMA; L, phi, chi |- U_cell covers unestablished selection, authentication, preparation, commit and disposal alternatives for this request and boundary
    ===>
    GAMMA; L, phi |- case(InterpretCell_a(P_b), chi, (z,r,state_req), unknown(U_cell))

  Cell-Port-Continue :=
    GAMMA; L, phi |- ContinueCell(InterpretCell_a(P_b), chi, z, B_next)
    GAMMA; L, phi, chi |- case(B_next, eta, y, outcome)
    ===>
    GAMMA; L, phi |- case(InterpretCell_a(P_b), chi and eta, (z,y), outcome)

  Cell-Port-Return :=
    GAMMA; L, phi |- case(P_b, chi, z, return(v, sigma, D))
    GAMMA; L, phi, chi |- a remains live at its cell delimiter
    ===>
    GAMMA; L, phi |- case(InterpretCell_a(P_b), chi, z, return(v, sigma, D))
```

These transition-failure cases arise while interpreting the request and are
not failures already reported by `P_b`. `state_req` is the same actual
post-operand request state in each rule. Selection or authentication failure
is only attached to the cell transition actually being attempted; a matching
nearer source handler still has precedence. Before a replacement is
committed, failure leaves the old root in place. A post-write disposal
failure instead records the actual committed replacement in `state_commit`;
it does not roll back or enter the normal `Unit` reply residual. The
failure-state and disposal cover are correlated with that very request and
phase and include possible later disposal failures and final host reports.
No rule promises that failure disposal completes. The
[generic cell steps](../../../spec/dynamic-semantics.md#scoped-cell-execution)
fix the preparation and replacement order.

If an applicable transition guard, failure state or disposal cover is not
established, `U_cell` may be the universal may-cover of the same request,
cell and surrounding context. It includes successful and failed transitions,
post-commit disposal, non-return and final observations as applicable; it
cannot establish a no-error claim or assume a normal reply. It does not
replace the requirement to cover external interpreter alternatives for
requests that are not selected by this cell.

The read and write premises include operation and actual-handle
authentication, successful preparation and, for replacement, its separate
retention proof. `cell_reply_transition` is the certified full post-reply
transition for the same selected builtin operation. It updates the resource
projection, removes the completed request frame as specified, and preserves
the applicable ordered control, other owners and outside facts; a resource
state alone is not a full continuation state. `D` records the cell-resource facts actually supplied for
the root, with their established completeness; it is not automatically a
complete backing or outside-owner interface. The write's `Unit` result has an
empty cell-owner cover, but that does not erase separately applicable outside
state or dependency facts. If a required reply fact is missing, residual
compatibility remains an obligation. A nearer source handler uses its own clause and actual reply;
an intercepted write is not a builtin update. A request that passes the cell
retains the cell boundary in its crossed control. The guarded forwarded-port
rule below supplies one source-handler resume case. The remaining cases below complete a conservative may-cover, subject to the
certified selection and external-interpreter interfaces.

The remaining cases of the cell interpreter are introduced from the same
covered body port, with no second examination of its producer. A request
selected strictly inside the cell is handled by that selected interpreter's
already established case and actual reply; it must not be mistaken for a cell
operation. A request selected outside the cell exposes the pending cell frame
in the new capture and keeps its selected clause continuation outside that
capture. For each actual reply its residual is rebuilt with the same cell
activation by `Cell-Forward-Restore`, the cell interpreter, and the normal
cell-close and outer frame producers. For a non-source outer interpreter its
own certified selection and reply contract supplies the corresponding case;
no source-clause facts are invented.

```sequent
family cell-port-other-cases:
  Cell-Port-Inner-Selection :=
    GAMMA; L, phi |- case(P_b, chi, z, request(r, K, R))
    GAMMA; L, phi, chi |- exact selected interpreter h lies strictly inside cell(a)
    GAMMA; L, phi, chi |- the established selected-interpreter case for this r is B_selected up to cell(a)
    ===>
    GAMMA; L, phi |- ContinueCell(InterpretCell_a(P_b), chi, z, InterpretCell_a(B_selected))

  Cell-Port-Forward :=
    GAMMA; L, phi |- case(P_b, chi, z, request(r, K, R))
    GAMMA; L, phi, chi |- the actual selection h lies outside cell(a)
    for each admissible actual outside reply q, state_q, deps_q:
      the same captured a is restored in state_restored
      R_cell(h,q,state_q,deps_q) = InterpretCell_a(R(h,q,state_restored,deps_q))
    ===>
    GAMMA; L, phi |- case(InterpretCell_a(P_b), chi, z, request(r, K ++ [cell(a)], R_cell))

  Cell-Port-Nonreturn :=
    GAMMA; L, phi |- case(P_b, chi, z, local_divergence(locality(cell(a))))
    GAMMA; L, phi, chi |- this same live cell(a) remains pending for the divergence
    ===>
    GAMMA; L, phi |- case(InterpretCell_a(P_b), chi, z, local_divergence(locality(cell(a))))

  Cell-Port-Failure :=
    GAMMA; L, phi |- case(P_b, chi, z, failure(origin, disposal))
    ===>
    GAMMA; L, phi |- case(InterpretCell_a(P_b), chi, z, failure(origin, AnyCellDisposal(a, disposal)))

  Cell-Port-Unknown :=
    GAMMA; L, phi |- case(P_b, chi, z, unknown(U))
    ===>
    GAMMA; L, phi |- case(InterpretCell_a(P_b), chi, z, unknown(TopCell(a, U)))
```

`AnyCellDisposal` is the universal may-cover of permitted disposal and final
report outcomes for that origin with the actual pending cell and surrounding
context. `TopCell` is the universal may-cover of the unknown behavior after
interpreting through this same cell, including all selections, replies,
non-return, failures and disposal. These top cases preserve the guard and
cell identity and prove no absence or successful completion. A more precise
certified disposal or unknown cover can replace them. Here `R_cell` ends at the cell delimiter without executing its close; the
outer frame composition supplies the actual close and the following port.
The `cell(a)` recorded in the request is the pending frame in the capture,
not a second close in that residual. The forward case is a conditional reply
family, not an assertion that the outside handler resumes;
its no-reply branch uses that selection's owned-discard cases. In the source
resume branch `Port-Forwarded-Cell-Resume` gives the detailed same-owner
construction. The recursive interpretation is guarded by an actual selected
request and reply: a conservative top is used where no certified residual or
selection case is available. Thus an unknown is not silently dropped to claim
coverage. For a finite case expansion, coverage follows by `C-Union` from the body's
certified cover, the exact selection cover and these cases. For each actual
request that may enter the cell interpreter, the cover must also include
selection and authentication failures, read/write preparation failures,
post-write-commit disposal failures and their boundary-aware disposal and
final reports, or the transition-specific universal fallback. Successful
read/write cases and failures already in `P_b` alone do not satisfy this
requirement. For a recursive
reply family, a guarded coinductive coverage certificate must cover every
finite observation and its next actual reply; otherwise use `TopCell` for the
unestablished branch. In either case retain top outcomes and unresolved
external interface obligations. This is a may-coverage claim,
not a termination or no-internal-error proof.

```sequent
Port-Resource-Body :=
  GAMMA; L, phi |- exact_selected_capture(r, k, K_b ++ [cell(a)] ++ K_out ++ [H])
  GAMMA; L, phi |- the restored cell is the same live activation a with its captured owner facts
  GAMMA; L, phi |- Port_r(K_b, cell(a), k, q, state, deps) = P_b
  GAMMA; L, phi |- the certified cell interpretation of P_b at a is P_cell
  GAMMA; L, phi |- T_cell is the certified cell-return and outer port to H
  GAMMA; L, phi |- each covered normal result of P_cell satisfies T_cell's crossing and close assumptions
  ===>
  GAMMA; L, phi |- Port_r(K_b ++ [cell(a)] ++ K_out, H, k, q, state, deps) = P_cell then_H T_cell
```

When the generic cell boundary is immediately inside `H`, the following
producer constructs that following continuation without a separate outer
port. `CellReturn_a(v,s,D)` is conditional on the actual normal body result
and the same activation `a` at `s`. Its alternatives retain their guards and
the same case witnesses:

| Cell-return alternative | Result at the outer delimiter |
| --- | --- |
| Result crossing is admitted and the ordinary release transition succeeds. | `return_at(H,v,s_out,D)`, where `s_out` is that transition's actual state, `a` is discharged once, and the body's `v` and `D` are preserved. |
| An applicable release, accounting or disposal phase fails. | The actual origin and failure state with the boundary-aware disposal and final-observation cover for that phase. |
| An applicable phase or its disposal cover is not established. | A covering unknown for the same return, activation and pending control. |

```sequent
Port-Cell-Body-Adjacent :=
  GAMMA; L, phi |- exact_selected_capture(r,k,K_b ++ [cell(a),H])
  GAMMA; L, phi |- the restored cell has the same live activation a and its captured owner facts
  GAMMA; L, phi |- Port_r(K_b,cell(a),k,q,state,deps) = P_b with its certified complete cover and reply residuals
  GAMMA; L, phi |- the established cell-port interpretation gives P_cell = InterpretCell_a(P_b) a complete guarded cover up to cell(a)
  for each covered normal result of P_cell, its actual value, state and dependencies admit the result-crossing premise or retain its obligation
  for each such result, CellReturn_a covers the applicable release transitions, their failures and disposal, or a covering unknown
  the same interpretation and return requirements hold for each admissible reply residual, with guarded coverage for an unbounded reply chain
  ===>
  GAMMA; L, phi |- Port_r(K_b ++ [cell(a)],H,k,q,state,deps) = P_cell then_H CellReturn_a with a complete conditional cover
```

The successful case uses `Frame-Cell-Return` and the same owner's accounting
transition. It uses the root at the body return, including writes performed
after restoration; neither the initializer root nor the capture-time root is
substituted for it. The return's dependency-crossing and external backing
obligations remain attached to that case. The result is at `H`, before `H`
executes; it does not select or discard the outer handler.

For the current ordinary non-worker generic-cell path, the evaluator pops the
frame, checks pending disposal, decrements the resource count and drops the
payload before continuing with the body's value. A drop can record a pending
failure after the owner has been removed; the actual `s_out` and subsequent
observation contract retain it. Do not reinterpret that case as a failed
pre-release transition or assume that reaching `H` proves no error. Worker
preflight and external backing use their own applicable contracts. The
[resource return](../../../src/eval/machine.rs#L3469),
[`J-Cell-Normal-Close`](first-slice-resource-rules.md#r6-capture-restore-and-completion)
and [cell execution](../../../spec/dynamic-semantics.md#scoped-cell-execution)
establish the sequence being related; the complete cover and any missing
crossing, disposal or guarded-residual proof remain explicit obligations.
Cell requests and their replies reuse `P_b` and its certified residuals; this
composition does not inspect the cell body again.

For a later request `r_next` exposed by `P_b`, suppose the selected source
handler is outside `cell(a)`. Its fresh clause owner `j` is distinct from
the consumed owner `k` of the earlier restoration. The matching residual
`R_b` below is the established residual of the **delimited body port**: after
an admissible actual reply it describes the remaining body only up to
`cell(a)`. It does not include the newly selected outer clause continuation.
The already certified `T_cell_outer` closes the cell only on a normal body
result and continues from that close through `K_outer` up to, but not through,
`H_outer`. It uses the actual state at the later body return, including any
cell writes after resumption.

The following projection follows from the same-owner move in
`H-Restore-Control` and the cell's established capture contract. The
`captured_cell` fact identifies the actual position, root and completion owner
in this selected capture; it is not inferred from a lexical `R` or a source
site. It is an input from that capture's certified interface, not a fresh
walk of it.

```sequent
Cell-Forward-Restore :=
  GAMMA; L, phi |- C_next = K_next ++ [cell(a)] ++ K_outer ++ [H_outer]
  GAMMA; L, phi |- captured_cell(C_next, a, v_capture, cell_owner)
  GAMMA; L, phi |- restore_control(j, C_next, state_q) = state_restored
  ===>
  GAMMA; L, phi |- restored_cell(state_restored, a, v_capture, cell_owner)
```

`restored_cell` records the same live activation, root and completion owner at
the restored cell position. It preserves their identity and obligations, not a
new copy or an additional acquisition. Other owner phases and outside facts
follow their respective interfaces.

```sequent
Port-Forwarded-Cell-Resume :=
  GAMMA; L, phi |- case(P_b, chi, z, request(r_next, K_next, R_b))
  GAMMA; L, phi, chi |- selected_clause(r_next, H_outer, payload, j, C_next, O_next, bindings, clause_entry)
  GAMMA; L, phi, chi |- C_next = K_next ++ [cell(a)] ++ K_outer ++ [H_outer]
  GAMMA; L, phi, chi |- resource_state_of(request_state(r_next)) = sigma_capture for this same request case
  GAMMA; L, phi, chi |- root(sigma_capture,a) = v_capture and a is live
  GAMMA; L, phi, chi |- captured_cell(C_next, a, v_capture, cell_owner) for this same activation and request case
  GAMMA; L, phi, chi, reply_case |- the same live j resumes with actual q_next, state_q and deps_q
  GAMMA; L, phi, chi, reply_case |- h_outer is this selection's interpreter context and actual clause continuation
  GAMMA; L, phi, chi, reply_case |- deps_q retains the actual reply's applicable cell, backing and outside facts
  GAMMA; L, phi, chi, reply_case |- restore_control(j, C_next, state_q) = state_restored
  GAMMA; L, phi, chi, reply_case |- Cell-Forward-Restore establishes restored_cell(state_restored, a, v_capture, cell_owner)
  GAMMA; L, phi, chi, reply_case |- R_b(h_outer, q_next, state_restored, deps_q) is the certified delimited body residual
  GAMMA; L, phi, chi, reply_case |- P_after [O_after] is a certified covering interpretation of R_b(h_outer, q_next, state_restored, deps_q) at cell a
  GAMMA; L, phi, chi, reply_case |- T_cell_outer [O_tail] is the certified cell-close and outer port to H_outer
  GAMMA; L, phi, chi, reply_case |- each covered normal result of P_after satisfies T_cell_outer's assumptions
  ordinary resource type, row, owner and structural usage premises hold independently of normal-return coverage
  ===>
  GAMMA; L, phi, chi, reply_case |- Port_r_next(K_next ++ [cell(a)] ++ K_outer, H_outer, j, q_next, state_restored, deps_q) = (P_after then_H_outer T_cell_outer) [O_after union O_tail]
```

`selected_clause` includes exact nearest selection and crossing of the actual
payload over the cell owner. The restore equation moves the same captured cell
frame, not a new activation, and consumes `j`; the outer clause's pending
continuation stays beyond `H_outer`. The earlier owner `k` is not made
available again. The rule assumes the indicated actual resume case: if the
outer clause discards instead, its no-reply and owned-close cases apply. It
does not require the capture to be discardable in order to resume.

The interpretation premise covers every applicable residual request,
non-return, failure and disposal, and unknown alternative under the same
guard and correlated state. `Cell-Port-Read` and `Cell-Port-Write` establish
individual cases, not that whole coverage by themselves. Unproved coverage or
compatibility remains in the corresponding obligations; an empty normal
return cover cannot dispense with the ordinary structural premises. Each
`O_tail` obligation is instantiated under its matching normal-result guard
and witnesses; the union preserves that scope instead of combining facts from
different cases.

This derives the earlier read-after-forwarding case. If the certified body
residual next requests a read of `a`, and the restored cell is its nearest
selected boundary, `Cell-Port-Read` returns the actual current root and the
same state. If no write occurs between capture and that read, the root is
`v_capture`; otherwise the read uses the root after those ordered writes. A
normal body return then enters `T_cell_outer`; it cannot release the cell
before the read or run the outer clause continuation before the selected
handler boundary. This is a conditional derivation from the delimited
residual, selection, cell and close contracts, not a proof that those
contracts cover every possible body behavior.

Exact selection must also account for a nearer matching builtin cell or source
handler. If `H` is inside the cell body, the cell boundary is outside its
capture and is not closed by abandoning that capture. Both rules use the
[resource composition](first-slice-resource-rules.md#r1r2-scope-and-row-composition)
and [cell execution](../../../spec/dynamic-semantics.md#scoped-cell-execution)
contracts; neither uses a type alone to prove dependency independence.

For a request in the source cleanup initializer, `f_cb` is the actual ordinary
Core binding frame for the callback, established by source lowering. It is
not a cleanup-specific initializer frame. `T_cb` performs `Frame-Binding` on
the actual returned callable, then follows any certified intervening context
query and the Core cleanup acquisition up to `H`. The conditional acquisition
uses `Core-Cleanup-Acquire` only after the same callback result has been bound
and the applicable query has returned. Its contract covers preparation
failure separately. There is no invocation owner to capture or run before
acquisition. This is the cleanup instance of `Port-Bind-Cross`, with the
source-to-Core callback correspondence made explicit.

```sequent
Port-Cleanup-Initializer :=
  GAMMA; L, phi |- f_cb is the lowered callback binding frame for this cleanup initializer
  GAMMA; L, phi |- exact_selected_capture(r, k, K_i ++ [f_cb] ++ K_out ++ [H])
  GAMMA; L, phi |- Port_r(K_i, f_cb, k, q, state, deps) = P_i
  GAMMA; L, phi |- T_cb is the certified callback binding, applicable context query, Core cleanup acquisition and outer port to H
  GAMMA; L, phi |- each covered normal result of P_i satisfies T_cb's binding entry assumptions
  GAMMA; L, phi |- T_cb retains the guarded query and acquisition entry obligations
  ===>
  GAMMA; L, phi |- Port_r(K_i ++ [f_cb] ++ K_out, H, k, q, state, deps) = P_i then_H T_cb
```

For a request within an acquired cleanup body, `cleanup(o, armed)` is the
same owner in the selected capture. `T_cleanup` uses the body's actual result
and dependencies, changes `o` from armed to running, invokes its certified
action once under the applicable context, and after a successful `Unit`
return discharges `o` and restores the saved body result before `K_out`.
Requests, non-return and failure in the action remain covered; invoking it is
not proof it terminates.

```sequent
Port-Cleanup-Body :=
  GAMMA; L, phi |- exact_selected_capture(r, k, K_b ++ [cleanup(o,armed)] ++ K_out ++ [H])
  GAMMA; L, phi |- restored owner o is armed with the same action and selected allocation context
  GAMMA; L, phi |- Port_r(K_b, cleanup(o,armed), k, q, state, deps) = P_b
  GAMMA; L, phi |- T_cleanup is the certified cleanup start, finish and outer port to H
  GAMMA; L, phi |- each covered normal result of P_b satisfies T_cleanup's assumptions
  ===>
  GAMMA; L, phi |- Port_r(K_b ++ [cleanup(o,armed)] ++ K_out, H, k, q, state, deps) = P_b then_H T_cleanup
```

A request made **during** a running cleanup action has a different pending
frame. Its certified port retains `o` running, the saved body result or owned
close continuation, and the unfinished completion. On a normal action return,
the frame finishes `o` and either restores the saved result or advances that
close; it does not invoke the action again. Capture and resume preserve that
phase. A discard cannot abandon a running owner or unfinished close, although
an action-local discard may be admitted when those obligations remain outside
its owned capture. The [cleanup phase](first-slice-close-rules.md#introduce-and-complete-one-cleanup-owner)
and [owned close](first-slice-close-rules.md#dependencies-and-the-discard-composition)
contracts supply these facts.

```sequent
Port-Cleanup-Running :=
  GAMMA; L, phi |- exact_selected_capture(r, k, K_a ++ [cleanup_running(o,saved)] ++ K_out ++ [H])
  GAMMA; L, phi |- restored owner o is running with the same saved result or close continuation
  GAMMA; L, phi |- Port_r(K_a, cleanup_running(o,saved), k, q, state, deps) = P_a
  GAMMA; L, phi |- T_finish is the certified finish transition and corresponding outer port to H
  GAMMA; L, phi |- each covered normal Unit result of P_a satisfies T_finish's assumptions
  ===>
  GAMMA; L, phi |- Port_r(K_a ++ [cleanup_running(o,saved)] ++ K_out, H, k, q, state, deps) = P_a then_H T_finish
```

For an ordinary body-result completion directly inside `H`, the following
producer constructs the previously conditional finish port. Write
`saved = saved(v,D_saved)` for the **same** value and dependencies retained
when this owner started. `Finish_o(saved)` applies to a covered action result
at the running completion. Its guarded alternatives are:

| Reached action or finish case | Result |
| --- | --- |
| The actual action result is represented by `Value::Unit` and the ordinary finish succeeds. | Discharge `o` once and return `v`, the actual post-finish state and `D_saved` at `H`. |
| Pending-disposal, Unit-representation or count checks fail, or another applicable finish/disposal phase fails. | Retain that phase's actual failure state, origin and boundary-aware disposal/final-observation cover. |
| A finish phase or its disposal cover is not established. | Retain a covering unknown for the same owner, saved result and pending control. |

The action's Unit result and its dependencies are not substituted for the
saved body result. The action and its actual request/reply residuals must
preserve the saved value and its metadata, and the established action and
finish transitions must establish that `D_saved` is still a sound dependency
cover for that value in the post-finish state. If that fact is missing, this
exact interface remains an obligation or covering unknown; a different
post-state cover needs its own certified finish interface. This does not
freeze the contents of cells reachable through the saved value. The success
case is `Frame-Cleanup-Finish`, followed by
`At_H`; a certified result-representation fact and the running-owner/count
contract can exclude the corresponding malformed-control guards. They do not
exclude pending or later disposal failures.

```sequent
Port-Cleanup-Running-Adjacent :=
  GAMMA; L, phi |- exact_selected_capture(r,k,K_a ++ [cleanup_running(o,saved),H])
  GAMMA; L, phi |- restored o is the same running owner with saved = saved(v,D_saved)
  GAMMA; L, phi |- Port_r(K_a,cleanup_running(o,saved),k,q,state,deps) = P_a with its certified complete cover and reply residuals
  GAMMA; L, phi |- the certified action and its residuals preserve saved and establish its dependency cover at each successful finish state
  for each covered normal action result, Finish_o(saved) has the complete guarded finish alternatives above for its actual state and result
  each other action case and admissible reply residual has its applicable port-frame cover, including guarded coverage of an unbounded reply chain
  ===>
  GAMMA; L, phi |- Port_r(K_a ++ [cleanup_running(o,saved)],H,k,q,state,deps) = P_a then_H Finish_o(saved) with a complete conditional cover
```

An action request carries the same running completion and saved result until
an admissible reply restores them. Exact selection decides the crossed
boundaries. A no-reply discard is admitted only if it does not abandon this
running owner or unfinished completion; an action-local discard with those
obligations outside its capture has its own close case. Non-return and failure
do not run finish as if the action had returned. The ordinary evaluator pops
the completion, checks pending disposal, checks the actual Unit representation,
then decrements the cleanup count before returning the saved value; a worker
preflight has a separate contract. See the
[cleanup completion](../../../src/eval/machine.rs#L3392) and
[`F-Cleanup-Finish-Valid-Control`](first-slice-failure-judgments.md#exclude-the-ordinary-cleanup-finish-control-failures).

The adjacent **armed** case constructs its continuation by starting the same
owner, then composing the certified action with that finish interface. On a
covered body return `v, s, D_saved`, `StartFinish_o` retains the following
alternatives: the actual start succeeds and enters the action with
`saved(v,D_saved)`; a start or preparation phase fails with its own state,
disposal and observations; or an unknown covers an unestablished start phase.
The successful action entry uses the saved allocation context and the
action's already certified delimited behavior, including all of its requests,
failures, non-return and admissible residuals. It starts the owner only once.

```sequent
Port-Cleanup-Body-Adjacent :=
  GAMMA; L, phi |- exact_selected_capture(r,k,K_b ++ [cleanup(o,armed),H])
  GAMMA; L, phi |- restored o is the same armed owner with its action and saved allocation context
  GAMMA; L, phi |- Port_r(K_b,cleanup(o,armed),k,q,state,deps) = P_b with its certified complete cover and reply residuals
  for each covered normal body result, StartFinish_o supplies all guarded start alternatives and the applicable certified action and Finish_o contracts for that same saved result
  each other body case and admissible reply residual has its applicable port-frame cover, including guarded coverage of an unbounded reply chain
  ===>
  GAMMA; L, phi |- Port_r(K_b ++ [cleanup(o,armed)],H,k,q,state,deps) = P_b then_H StartFinish_o with a complete conditional cover
```

`Frame-Cleanup-Start` establishes the successful armed-to-running transition;
the same action and `Finish_o` handle its actual outcomes. The evaluator's
[ordinary cleanup start](../../../src/eval/machine.rs#L3372) checks and
reserves before pushing the completion and beginning the action. A failed
start does not prove that the action ran. Neither rule above supplies the
different continuation of an owned close, for which the saved continuation is
`CloseRest` rather than a body value; that case uses `Frame-Close-Finish` and
the owned-close contracts. Missing action ports, owner/representation facts,
transition cases or guarded residual coverage remain explicit obligations or
covering unknowns, never a reason to recheck the action or captured segment.

### A cleanup action running in an owned close

An owned discard has a different saved continuation from ordinary cleanup
return. Let an earlier discard of `k0` own plan `P = cleanup(o,A) ++ P_rest`
at this cleanup's actual position, with surviving continuation `D`. Its
successful preflight and subsequent successful transfer have already consumed
`k0` and any nested live clause capabilities taken by that transfer, and have
scheduled their plans. Reaching `cleanup(o,A)` in that plan does not consume
those capabilities again. The same plan and continuation may be represented
by physical owner frames and a close-completion frame, or by the applicable
logical close interface; no particular extra marker is assumed.

Suppose this same cleanup start has succeeded, and its action later makes
request `r` selected by `H` with fresh owner `k`. Here `k` is the new action
request's owner, distinct from `k0` and every already consumed nested owner.
After an actual successful reply restores `k`'s capture, the action continues
up to its running completion. `CloseRest(P_rest,D)` is the **same** pending
remainder and survivor, with a certified conditional port `B_rest` through
the actual remaining control up to `H`. It does not include execution beyond
`H`. It retains the existing outside tickets, their routes and any saved
values in `D` under their own contracts. An ordinary saved body result is not
invented for the abandoned cleanup body.

```sequent
Port-Cleanup-Owned-Close-Running :=
  GAMMA; L, phi |- preflight and successful transfer of k0 scheduled the same P and D, and consumed k0 and the transferred nested live clause tickets once
  GAMMA; L, phi |- the certified plan reached cleanup(o,A) and its successful start made o running with CloseRest(P_rest,D)
  GAMMA; L, phi |- selected_clause(r,H,payload,k,C,O0,bindings,entry_k) for this actual action request, with k fresh and C = K_a ++ [cleanup_running(o,CloseRest(P_rest,D))] ++ K_out ++ [H]
  GAMMA; L, phi |- the actual reply q with deps satisfies r's reply and crossing premises and this same successful restore consumes k, yielding state with o, pending CloseRest and their established tickets restored
  GAMMA; L, phi |- Port_r(K_a,cleanup_running(o,CloseRest(P_rest,D)),k,q,state,deps) = P_a with its certified complete cover and reply residuals
  for each covered normal action result, the actual finish alternatives and the same B_rest up to H are certified under its correlated result and post-state
  all other action, finish and close-rest cases have their applicable request, non-return, failure and disposal covers or covering unknowns, including guarded coverage of unbounded replies
  ===>
  GAMMA; L, phi |- Port_r(K_a ++ [cleanup_running(o,CloseRest(P_rest,D))] ++ K_out,H,k,q,state,deps) = P_a then_H FinishClose_o(B_rest) with a complete conditional cover
```

On an actual `Unit` action return, a successful `Frame-Close-Finish` discharges
the **running finish** ticket once and enters `B_rest` at the actual
post-finish state. It does not restart `A`, consume `k0` or a nested ticket
again, or return directly to `D`. `B_rest` runs the remaining owned positions
in their established order; the close-end contract eventually supplies `Unit`
to `D` only on its own successful case. A pending disposal failure and the
outside tickets and saved values are carried by the actual state and the
certified continuation, not assumed unchanged by an action effect.

Requests from the action or rest retain their own actual selection and
residual. A further selected source handler may resume the same pending finish
and rest; a no-reply path must independently prove that it does not abandon
the running owner or unfinished close. Failure, divergence and unknown cases
remain covered and do not reach `B_rest` as though finish succeeded. The
[owned-close tickets and route](first-slice-close-derivation-rules.md#produce-and-transport-tickets-through-owned-close)
supply the conditional start, finish and survivor contracts; the
[discard transfer](#no-reply-and-owned-close) supplies the earlier ownership
timing. A missing bounded `B_rest`, survivor route, saved-value preservation,
or complete finish/transition cover remains an obligation or covering
unknown, not a reason to inspect the certified action or rest again.

These equations are conditional, not a completeness proof. In particular,
`T_let`, `T_out`, `T_acquire`, `T_cell`, `T_cb`, `T_cleanup`
and `T_finish` must be certified
interfaces that cover their actual post-state, owner and failure behavior.
The current records do not yet derive all of those ports or the complete
boundary-aware failure/disposal relation. A checked constituent with only a
whole-expression residual cannot be reopened to obtain them. The concrete
counterexample below shows why that missing delimited relationship is material.
An opaque function, method, native boundary or recursive callable must supply
its established applicable port and assumptions as an outside-slice input;
these rules neither check its definition nor prove its recursive contract.

### No reply and owned close

On an ordinary discard, the established [owned-close judgment](first-slice-close-rules.md#dependencies-and-the-discard-composition)
supplies the same live `k`, its plan `P_close`, the surviving clause control,
the residual close row and separate ownership, interpreter, dependency and
outside-completion proofs. It does not claim the plan has finished. For one
conditional case the no-reply behavior is below. `scheduled_close(s,P,D)`
is a logical interface for the actual successful transfer, not a claim that a
physical `CLOSE` frame always exists. It retains the same plan, actual owner
positions and surviving `D` in both cases:

- When the transfer schedules no physical close-owner frames, its active
  control is a pending `Unit` return directly into `D`; no `CloseCompletion`
  frame is installed. A logical plan may still record nested capabilities
  that were consumed during the transfer and have empty inner plans.
- When it schedules one or more physical close-owner frames, those frames
  are in their established structural order ahead of `CloseCompletion` and
  `D`; the active control is a pending `Unit` return into that close control.

Both cases preserve the same surviving outside owners. The transfer also
consumes nested live clause capabilities and moves their owned inner plans
into the scheduled structural order; it does not keep those nested owners
live for a second consumption at the later close cursor. The consumed nested
tickets below are logical post-transfer facts, not retained physical clause
frames. Any pending disposal
failure from dropping abandoned control remains a separate case before the
next source step. The distinction follows the current
[discard implementation](../../../src/eval/machine.rs#L5438) and the
[nested plan account](first-slice-close-derivation-rules.md#compose-an-owned-plan).

```sequent
H-Discard-No-Reply :=
  GAMMA; L, phi |- selected_clause(r, H, payload, k, C, O, bindings, clause_entry)
  GAMMA; L, phi |- control(state) = F ++ [CLAUSE(H,k,live(C))] ++ O
  GAMMA; L, phi |- owner(state,k) = live(C)
  D = F ++ [CLAUSE(H,k,consumed)] ++ O
  GAMMA; L, phi |- discard(k) : Unit ! epsilon_close ; consumes(k), for each case schedules_under(phi_i, P_i, D_i)
  GAMMA; L, phi |- (phi_i, C, D_i, P_i) is the same covered selection and actual capture activation
  GAMMA; L, phi, phi_i |- P_i = P_close and D_i = D
  GAMMA; L, phi, phi_i |- discard preflight succeeds before consuming k or moving C
  GAMMA; L, phi, phi_i |- the subsequent successful transfer moves this C into its scheduled close and produces post_transfer
  GAMMA; L, phi, phi_i |- post_transfer records owner(k) and the plan's nested clause tickets as consumed and preserves the same outside owners
  GAMMA; L, phi, phi_i |- scheduled_close(post_transfer, P_close, D)
  GAMMA; L, phi, phi_i |- B_close covers this P_close before this D from post_transfer
  ===>
  GAMMA; L, phi and phi_i |- no_reply_case(r, k, B_close, D, post_transfer)
```

The discard expression's local success behavior is obtained directly from
that same no-reply case. It covers the scheduled close up to the surviving
continuation `D`: a normal result is `Unit` only after the close completes.
The caller composes `D` separately, once. A failure of discard preparation is
another case, before consuming the owner; subsequent internal disposal has its
own contract and can change the final observation. These introductions bind
the same selected request and actual owner as the owned-discard judgment.

```sequent
family discard-expression-cases:
  Discard-Close :=
    GAMMA; L, entry, phi |- no_reply_case(r, k, B_close, D, post_transfer)
    ===>
    GAMMA; L, entry |- continue_under_case(discard_behavior(k), phi, (r,k,D,post_transfer), B_close)

  Discard-Preflight-Failure :=
    GAMMA; L, entry, phi |- selected_clause(r, H, payload, k, C, O, bindings, clause_entry)
    GAMMA; L, entry, phi |- owner(state,k) = live(C)
    GAMMA; L, entry, phi, chi |- discard preflight fails for this k and C at state_fail with origin
    GAMMA; L, entry, phi, chi |- state_fail still records owner(k) = live(C) and unchanged capture accounting
    GAMMA; L, entry, phi, chi |- disposal_fail covers this failure and final observations from state_fail
    ===>
    GAMMA; L, entry |- case(discard_behavior(k), phi and chi, (r,k,C,state_fail), failure(origin, disposal_fail))
```

The preflight guard and failure state require the applicable justified
primitive table. If they are not established, the discard cover retains an
unknown that includes preflight failure and disposal. It cannot assume
success or establish the closed no-error conclusion. If preflight succeeds,
later failures and requests belong to `B_close` and its component contracts;
they are not preflight failures and do not undo actions already performed.

`B_close` includes action and boundary contracts in structural order: an
action's normal completion advances the close, while its request, non-return
or failure remains covered without entering the later continuation as though
it completed. A successful completed close returns `Unit` to the surviving
clause continuation; neither it nor this judgment resumes the abandoned
segment. A certified plan must supply its close behavior interface; a new plan
composition combines already established component behaviors. Do not reconstruct
that behavior by traversing an opaque certified capture or action. This rule is
conditional on the separate close premises, including actual action
interpretation and the least row; a close schedule is not a termination proof.

For a newly formed plan, the following rules construct close behaviors from
established component behaviors. `SeqUnit` is the existing strict sequencing
composition specialized to a `Unit` result; it carries requests with the rest
of the close pending and enters the second component only on normal completion
of the first. `F_rest` is one certified continuation parameterized by the
actual post-close state and dependencies, not a recheck of the rest of the
plan. Each premise is conditional on its own case and structural position.

```sequent
family owned-close-behavior:
  H-Close-Empty-Marker :=
    GAMMA; L, phi |- the owned plan has no remaining close entries and close preparation succeeded
    GAMMA; L, phi |- control(state) = CLOSE :: D
    GAMMA; L, phi |- completing this marker succeeds and produces state_out with control D
    ===>
    GAMMA; L, phi |- success_case(close_behavior([], D, state), phi, return((), state_out, {}))

  H-Close-Empty-Direct :=
    GAMMA; L, phi |- the owned plan has no remaining close entries and close preparation succeeded
    GAMMA; L, phi |- control(state) = D and the actual pending control is return Unit
    GAMMA; L, phi |- no physical close marker was scheduled and the direct entry to D succeeds
    ===>
    GAMMA; L, phi |- success_case(close_behavior([], D, state), phi, return((), state, {}))

  H-Close-Nested-Clause :=
    GAMMA; L, phi |- the next logical plan entry is consume(j,P_inner,position) followed by rest
    GAMMA; L, phi |- the successful outer discard transfer already consumed this same j and left P_inner pending at position
    GAMMA; L, phi |- B_inner_rest is the certified close behavior of P_inner followed by rest for the same D and state
    ===>
    GAMMA; L, phi |- close_behavior(consume(j,P_inner,position) ++ rest, D, state) = B_inner_rest

  H-Close-Action :=
    GAMMA; L, phi |- first plan component is armed action a at position i
    GAMMA; L, phi |- start_action(state, a, i) = state_running
    GAMMA; L, phi |- action a has certified invocation behavior B_a from state_running at position i
    GAMMA; L, phi |- F_rest first finishes a and then uses the certified rest behavior
    GAMMA; L, phi |- each covered normal Unit result of B_a satisfies those assumptions
    ===>
    GAMMA; L, phi |- close_behavior(action(a) ++ rest, D, state) = SeqUnit(B_a, F_rest)

  H-Close-Boundary :=
    GAMMA; L, phi |- first plan component is owned boundary b at position i
    GAMMA; L, phi |- b supplies certified close behavior B_b from state at position i
    GAMMA; L, phi |- certified rest behavior is F_rest under its post-close assumptions
    GAMMA; L, phi |- each covered normal Unit result of B_b satisfies those assumptions
    ===>
    GAMMA; L, phi |- close_behavior(boundary(b) ++ rest, D, state) = SeqUnit(B_b, F_rest)
```

The empty rules describe separate successful close cases, not a guarantee that
preparation, pending disposal or marker completion cannot fail. In the direct
case `state` is the actual pending `Unit` return into `D`; the rule does not
invent or remove a physical marker. A plan that records already-consumed nested
clauses advances by `H-Close-Nested-Clause`: the rule interprets the pending
inner plan before the rest and does not perform another physical consumption.
If those plans have no owner entries, they reach the same empty close behavior.
The `{}` is the dependency cover of `Unit`, not a replacement
for other applicable outside facts in the state. `start_action` changes this armed owner to running before
invocation. `B_a` is the action's invocation under the actual closing
context, including its running owner and unfinished close; the ordinary
callable contract alone is insufficient. `B_b` covers the owned boundary's
success and any applicable failure, without asserting an unmodeled effect.
After a normal action return, `F_rest` first discharges that running owner
using its established finish transition and only then advances the close.
Nested owned captures use their already certified close behavior at their
structural position. These rules do not decompose a previously certified plan
or claim that any component terminates. Failure disposal still requires its
own supplied coverage, including failures occurring after earlier actions ran.

### Remaining information required by these rules

Ordinary request/result types, row and a whole-expression reply residual do
not determine the delimited port. For example, after an `Int` reply `q`, one
selected segment can return `q + 1` to a clause that adds `1`, while another
can return `q + 2` to a clause that returns it unchanged. Both whole residuals
return `q + 2`, but their segment results and clause continuations differ.
Substituting the whole residual for either segment would put clause work on the
wrong side of the handler. A certified `Port` and clause continuation
relationship distinguish them without rechecking either body.

Likewise, the same cleanup action type and effect row can describe an action
that returns and one that diverges. An owned plan and its row alone cannot
derive `B_close`; each actual action needs its established behavior, and an
opaque plan needs a compositional close interface. Failure requires another
boundary input: an originating failure alone does not determine disposal
behavior or the final report. Missing these facts leaves explicit obligations,
not a proof of normal return or a completed rule. How all in-slice producers
establish and transport `Port`, plan behavior, complete failure/disposal and
their guarded coverage without repeating constituent verification remains
open. These counterexamples prevent claiming that the rules above alone close
the first-slice calculus or justify retiring any check.

## Worked cases

For an inner `Ask` handler whose `ask` clause evaluates `let v = resume 1;
v + 1`, the captured body segment may return `1` to the clause continuation.
`H-Resume-Case` then composes the certified addition, so the whole handler can
return `2`. A binding around that whole handler receives `2`, not the reply
or segment result `1`. If the clause discards the inner capture and returns
`7`, its no-reply branch can instead make the handler return `7`; it does not
run the abandoned segment. These are conditional examples; ordinary Ash
operation, arithmetic, allocation and row premises still apply.

For an exposed `E<T>.op` below an `E<U>` boundary and an outer `E<T>`
boundary, an established `T = U` selection chooses the inner boundary. An
established inequality passes it and can select the outer boundary. Without
either fact, both alternatives are covered with their own capture, crossing
and completion obligations. The two abstract alternatives need not both
occur. A discard must satisfy the owned-close rule for every covered relevant
selection; a resume does not acquire an unrelated discard-safety premise.
These examples are not evidence that the current compiler retains the proposed
certificates.

## Remaining obligations and current consumers

The rules give conditional introductions and composition for new in-slice
frames, source capture and resume, guarded cell interpretation and close
behavior. Their conservative top cases supply may-coverage without assuming
success or an impossible failure. They do not establish admission of every
composition: a top case cannot prove the dependency, completion, row or
no-internal-error facts that a consumer requires. The precise remaining
requirements are:

- an opaque operand, action or callable must supply its certified conditional
  behavior and applicable dependency, reply and state interface as an external
  boundary fact. Neither an ordinary type nor its effect row determines those
  facts; no function body is checked here;
- every recursive residual needs a guarded covering certificate or a top
  alternative. A cyclic assertion of coverage alone proves nothing, and a
  top alternative may prevent a consumer from proving admission;
- exact request selection and its correlated payload, capture, state and
  reply facts must be established or conservatively covered. Missing facts
  cannot be filled from a different activation or case;
- the normal frame steps are conditional on the actual pattern, retention,
  crossing, allocation and owner premises. Failure and disposal remain in the
  cover unless their guards are independently discharged; and
- worlds, guards, delimited ports and scoped obligations are candidate
  mathematical interfaces. Their representability and the soundness and
  preservation of these compositions remain to be established. The existing
  checks stay in force pending the separate validation decision.

These are boundaries of the present rules, not a request to recheck certified
fragments, inspect opaque captures or develop function checking and linking.

Current [request elaboration](../../../src/elaborate.rs#L13966),
[control construction](../../../src/core/capture.rs#L2214),
[selection and completion analysis](../../../src/core/capture/control.rs#L5966)
and [linked Core validation](../../../src/core/validate.rs#L13857) have
separate subjects and consumers. Their graphs are not the certificates defined
above. They remain in force; no single composition rule authorizes deleting
shared analysis. System-level coverage, preservation and narrow-correctness
proofs are separate from checking a program or fragment against these rules.
