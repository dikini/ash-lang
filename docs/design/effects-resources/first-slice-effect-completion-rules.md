# First Slice: Effect and Completion Rules

This record develops the E1–E10 effect and control families in the
[catalogue](first-slice-catalogue-and-map.md#effect-handler-and-control-rules).
It composes the established judgments in the
[request and sequencing](first-slice-request-sequencing-judgments.md),
[normal-return](first-slice-normal-return-judgments.md),
[nearest-boundary](first-slice-nearest-boundary-judgments.md), and
[one-shot usage](first-slice-continuation-use-trace.md#candidate-usage-judgments)
records. The rules below are candidate type-system rules, not current Ash
syntax, implemented certificates, or a completed calculus. The
[specification](../../../spec/README.md) is authoritative for current Ash.

The intended boundary is a certified constituent judgment with its type,
row, behavioral facts and explicit assumptions. A new composition checks its
own relationships, but does not recheck a constituent or traverse its body or
a graph to rediscover its established behavior. Conditional judgments retain
their conditions. A named premise is not evidence that Ash can express or
prove it. Missing premises remain obligations; no unconditional conclusion
follows. The representation and transport of open obligations remain open.
Surface checking may infer facts; typed Core must retain complete resulting
types and the facts needed for the slice. This does not require source
annotations or select a certificate representation.

The effect and handler rules apply the same general type and proposition
judgments to the authenticated contracts of the actual declarations. A
different effect or operation does not introduce a dedicated typing rule,
verification pass or recheck of a certified implementation. An effect row
is a coarser projection of effect requirements; the operation, handler and
control contracts retain the additional behavioral facts and obligations
needed by the composition. Concrete operation examples and implementation
traces in this record are contract instances and correspondence evidence,
not specialized checkers. Establishing that the general rules and declared
contracts cover those concrete cases remains required.

Ordinary function and data typing are outside the slice. Opaque values and
computations bring their established dependencies and control contracts; a
polymorphic value is not assumed resource-independent. Private Store control,
regions, registrations, native and network resources are outside this record;
their applicable boundary facts and obligations still have to be preserved.

## Declarations, instances and rows: E1–E3

An effect declaration establishes a stable effect identity, its ordered
parameter kinds and nonempty operation set. Each distinct operation identity
belongs to that effect and has exactly one pure outer `P -> Q` signature;
operation-local parameters and requirements are not admitted. Its public API
exports the authenticated declaration as a whole. These facts come from the
[current declaration rule](../../../spec/static-semantics.md#effects), not
from the spelling or a body discovered at a use. A declaration does not prove
an interpreter implementation satisfies its contract.

The following declaration rule consumes the established kind and signature
judgments for the declaration's members. Its conclusion is the declaration
contract that the instance rule consumes. `sigma` substitutes the complete,
well-kinded argument vector for the declaration parameters. `remove` and
`union` are the partial operations of the
[computation type rules](../../../spec/static-semantics.md#computation-types-and-effect-rows),
not arbitrary set operations on unknown tails.

```sequent
family effect-declarations-and-rows:
  J-Effect-Declaration :=
    E and its operation identities are fresh for the defining module
    the ordered effect parameters have admitted kinds, none EffectRow
    the nonempty operation list has distinct names and identities owned by E
    each operation has a well-formed pure outer P -> Q signature under the parameters
    no operation has local parameters or requirements
    ===>
    GAMMA |- effect_declaration(E, parameters, operations, visibility)

  J-Operation-Instance :=
    PHI(E) establishes parameter kinds and operation op : P -> Q
    arguments have the declared arity and positional kinds
    sigma is the capture-avoiding substitution of arguments for those parameters
    ===>
    GAMMA |- operation(E<arguments>, op) : sigma(P) -> sigma(Q)

  J-Row-Compose :=
    GAMMA |- epsilon_1 row ok
    GAMMA |- epsilon_2 row ok
    the specified partial union of epsilon_1 and epsilon_2 succeeds as epsilon
    ===>
    GAMMA |- epsilon_1 union epsilon_2 = epsilon

  J-Row-Remove :=
    GAMMA |- epsilon row ok
    epsilon explicitly establishes the exact instance I
    the specified exact removal succeeds as rho
    ===>
    GAMMA |- epsilon remove I = rho
```

Row formation, equality, substitution, unification and weakening retain their
specified kind, occurs and lacks conditions. Written duplicates reject;
inferred union coalesces equal members. Different effect identities do not
match, and all argument positions participate in equality. A substitution
preserves applicable facts and cannot invent lacks or inequality. Two distinct
parameters may instantiate equally. An unknown tail is not a proof of absence
or explicit membership; failed or ambiguous partial operations do not establish
a row. A row is an unordered requirement, not a schedule or a proof that a
request occurs. These schemas use the specified row relations; they do not
provide a new solver or establish their implementation correspondence.

### Effect-parameter interface requirements

An effect's parameters may need an interface requirement shared by every
instance of that declaration. For example, a proposed `Failure<E>` could
require `Error<E>`; these names illustrate the general rule, not existing Ash
syntax or a failure-specific checker. Current [effect declarations](../../../spec/syntax.md#grammar)
do not have such a requirement, and current
[`WF-Effect-Instance`](../../../spec/static-semantics.md#computation-types-and-effect-rows)
checks identity, arity and kinds without one. The following is a candidate
extension. Until specified and implemented, `J-Effect-Declaration` and
`J-Operation-Instance` above describe the current unbounded case.

Let the authenticated declaration of effect `E` bind ordered parameters
`alpha` and carry a well-scoped ordered interface-requirement template
`Req(alpha)`, alongside its operation contracts. Its declaration judgment
establishes the requirements' interface identities, kinds, scope and
visibility under those same parameters; naming a requirement does not prove
it. A public effect's interface must retain the template and the facts needed to
authenticate it without exposing an implementation body.

```sequent
J-Form-Effect-Instance-With-Requirements :=
  SIGMA(q_E) = certified declaration E(alpha) with Req(alpha), operations and obligations O_decl
  GAMMA |- args have E's ordered arity and positional kinds
  sigma maps alpha to args, preserving scope, binders and kinds
  for each requirement Q in Req(sigma), the same GAMMA supplies certified evidence e_Q for exactly Q under this substitution and scope, or retains Q as a scoped obligation O_need(Q)
  M is the ordered mapping from each requirement occurrence Q to that exact e_Q or O_need(Q), including its applicable scope, provenance and symbolic capture dependencies
  the required uses in M jointly fit each evidence modality and the applicable symbolic authority interface, including each prescribed case-indexed disposition A, or retain the scoped obligation O_modality
  O_instance carries O_decl[sigma], the applicable evidence's inherited obligations, every O_need(Q) and O_modality, with their original assumptions, guards and binders
  ===>
  GAMMA |- instance(q_E, E<args>, sigma, Req(sigma), M, A) [O_instance]

J-Use-Required-Effect-Operation :=
  GAMMA |- instance(q_E, E<args>, sigma, Req(sigma), M, A) [O_instance]
  q_E authenticates op as E's operation with signature P -> Q under alpha
  ===>
  GAMMA |- operation(E<args>, op, M, A) : P[sigma] -> Q[sigma] [O_instance]
```

The conclusion is conditional when any required evidence or inherited premise
is outstanding; `O_need` is not an implementation of the interface. The
ordinary request or handler rule composes this instance judgment with its own
operand, selection and control obligations. Row and type formation, handler
targets and imported or public interfaces must preserve the applicable same
instance and its requirements; a boundary may forward a scoped requirement
where the chosen interface permits it. The precise formation owners, evidence
selection and permitted conditional boundaries remain to be specified. These
rules do not assume that a requirement's implementation or a law is proved by
the declaration alone.

A polymorphic boundary may abstract over `alpha` and the applicable evidence
or outstanding obligations. Its later user specializes that established
interface; it does not check the declaration or an implementation body again:

```sequent
J-Specialize-Required-Effect-Instance :=
  SIGMA(q) = certified(GAMMA_0 |- instance(q_E, E<args>, sigma, Req(sigma), M, A) [O_instance])
  theta is an explicit, kind-correct capture-avoiding specialization respecting q's binders and rigid identities
  GAMMA |- the specialized assumptions of GAMMA_0 hold for this same use, or retain them as scoped O_fit
  the same theta specializes args, Req(sigma), M, A, its applicable evidence, assumptions and O_instance together without reselecting established evidence
  for each applicable guarded case c of this use, M[theta] and A[theta] jointly fit that same case's capability identities, available authority, modalities and prescribed dispositions, or retain scoped O_authority_special(c)
  O_result carries O_instance[theta], O_fit, each O_authority_special(c) and every inherited evidence obligation under the same specialized guards and binders, universally binding local case witnesses when their scope is exited
  ===>
  GAMMA |- instance(q_E, E<args[theta]>, sigma followed by theta, Req(sigma)[theta], M[theta], A[theta]) [O_result]
```

Instantiation can identify previously distinct parameters; any needed
inequality remains a separate established fact or obligation. Equal types do
not by themselves identify actual capabilities, and distinct formal
parameters do not guarantee distinct capabilities after specialization. The
joint fit uses the actual case-correlated capability relation, represented
symbolically where necessary, and respects each evidence modality without
duplicating or dropping authority. It checks the new use, not the certified
evidence again. The effect's
current exact identity remains `EffectId` plus its complete instantiated
argument vector. An interface constraint neither changes that identity nor
creates a wildcard handler. Whether and how selected evidence affects an
operation or handler's behavior, dependencies or dispatch is a separate
correspondence and design question; any applicable evidence identity and
scope must be retained rather than silently discarded. `M` records the actual
selected evidence or corresponding outstanding obligation for each requirement;
equal interface goals do not make distinct lexical evidence sources or their
dynamic captures interchangeable. The mapping is a scoped interface, not a
requirement to package future runtime captures as compile-time values. A later
discharge can supply appropriate evidence for an unresolved obligation without
reselecting evidence already established for another occurrence. How row
coalescing preserves applicable evidence when identities coincide remains a
separate design obligation. `A` is a symbolic authority interface, not an
actual runtime owner or automatic consumption at instance formation. Joint fit
must account for all required uses together; it cannot duplicate or silently
drop authority contrary to its policy. Operation application checks the actual
case against that interface using the general authority rules. At the Core boundary,
the resulting types, substitutions, symbolic requirements, evidence references
and scoped obligations are explicit; checking a new composition uses them
without inferring them from a constituent or repeating its proof. Source
inference may supply them. No concrete Core format or new surface syntax is
chosen here. Reusing evidence follows its established scope and modality; a
reference to it does not duplicate runtime authority it may describe.

### A finite closed-row least union

Handler admission below requires least-row evidence. One general case can be
produced directly from the existing row algebra, rather than treating that
evidence as an unexplained handler premise. Let `rows` be a finite family of
already certified, well-formed **closed ground** rows in the same context:
their exact effect identities and arguments have no remaining substitution
that can change equality. Let `ClosedGround` be the admitted closed ground
rows in that context and `leq` the specified row-weakening relation. `union`
is inferred union, which coalesces equal instances; it is not a written row
containing duplicate members.

```sequent
J-Finite-Closed-Row-Least :=
  GAMMA; Phi |- rows = [epsilon_1, ..., epsilon_n] and each epsilon_i is a certified well-formed closed ground row [O_rows]
  GAMMA; Phi |- fold_union([], rows) = epsilon using the specified partial inferred union [O_union]
  O_least carries O_rows, O_union and any new proof obligations under their original subject, guard and witness scopes
  ===>
  GAMMA; Phi |- epsilon is well formed and is the least ClosedGround row above every epsilon_i under leq [O_least]
```

The base of `fold_union` is the empty row. For any admitted closed ground
candidate `zeta`, the specified idempotent set union is included in `zeta`
exactly when every input is included in `zeta`. This supplies both the upper
and leastness directions; an empty input family yields the empty row. The
rule composes the row facts already published by its inputs, not their
implementations. This finite argument is a property of the general row rules;
it does not require running a proof over each execution.

For a handler, the inputs can be its established body remainder and the
certified direct requirement rows of **every syntactic clause**, even when a
clause is behaviorally unreachable. A direct same-instance request in a clause
remains a requirement. A clause's checked row already widened to the shared
handler output does not by itself reveal its exact direct contribution, and
the continuation's recursive output row cannot simply be subtracted from it.
The clause certificate must independently supply the required direct-row
relationship, including operand and applicable discard requirements, or that
producer remains an obligation. Ordinary clause and structural typing remain
separate.

This rule is deliberately limited to the `ClosedGround` comparison domain.
It does not establish a symbolic least row among open or polymorphic rows,
solve recursive row equations or manufacture a missing clause contribution.
A handler conclusion whose specified leastness ranges over a broader admitted
domain needs the additional corresponding proof. Specialization that can
coincide symbolic instances requires the separately guarded substitution and
row evidence; failure to prove a partial operation does not establish absence.
The current [handler rule](../../../spec/static-semantics.md#effects) and
[row algebra](../../../spec/static-semantics.md#computation-types-and-effect-rows)
are the specification for this correspondence. Core's
[`least_handler_output`](../../../src/core/validate.rs#L16414) currently
reconstructs direct row contributions; replacing that consumer requires a
certified producer for the same inputs and scope, not just this union lemma.

## Request and handler admission: E4–E5

For E4, use `J-Perform-Behavior` and its normal-return relation in the
[sequencing record](first-slice-request-sequencing-judgments.md#candidate-rule-introduce-a-request).
The operation contract gives domain `P` and result `Q`; the certified operand
must have `P`, and partial union must establish its row plus the exact lexical
instance. Its normal result supplies the actual payload. `E-Perform-Operand`
saves the request's lexical instantiation **before** operand evaluation.
An operand request retains the pending request frame; abandonment or
non-return does not introduce the later request through that frame. Neither
its row nor the request judgment selects a handler. The reply contract is
supplied by the selected interpreter and preserves its actual dependencies and
resulting context; the ordinary type `Q` does not establish independence.

The following E5 schema describes ordinary handler admission. `B_body` and
`B_i` are already established behavioral judgments; `k_i` is fresh for its
clause activation. The symbolic `case_i` identifies the correlated payload,
capture and context supplied at a selection. A clause's ordinary type, row
and scope are established independently of its behavioral assumptions
`psi_i(case_i)`. Both projections come from the same certified clause, not
two checks of its body. `rho` is the exact body-row remainder and `epsilon_out`
is the least row satisfying its inclusion and all clause requirements under
the current handler rule. The conclusion's `HandleBehavior` must satisfy the
case obligations immediately below; it is a candidate contract, not an
implementation operation.

```sequent
J-Handle-Composition :=
  GAMMA |- body : A ! epsilon_body ; B_body
  GAMMA |- epsilon_body remove I = rho
  the clauses cover each operation of I exactly once with irrefutable checked patterns
  for every instantiated op_i : P_i -> Q_i, k_i is fresh and
    GAMMA, bindings(pattern_i : P_i); k_i : resume(Q_i, A, epsilon_out)
      |- ordinary(clause_i) : A ! epsilon_out
  for every i and fresh symbolic case_i,
    GAMMA, bindings(pattern_i : P_i); k_i : resume(Q_i, A, epsilon_out), psi_i(case_i)
      |- behavior(clause_i) : B_i(case_i)
  ordinary(clause_i) and behavior(clause_i) are projections of one certified judgment
  for every i, U(k_i, clause_i, available, consumed)
  epsilon_out is the least row satisfying rho and every clause requirement
  for every covered selection case, its established facts entail the matching psi_i
  the handler behavior cases and all their selection and crossing premises are established
  ===>
  GAMMA |- handle body with I { clauses } : A ! epsilon_out ; HandleBehavior(B_body, B_i, I)
```

The final premise requires a coverage-preserving composition, not merely the
name `HandleBehavior`. For every applicable certified body case:

- A normal body return passes its actual `A` value and facts outward after
  removing this handler boundary. No source return clause runs.
- A request selected at this handler uses its actual payload and established
  pattern facts, introduces a fresh clause owner and runs the matching
  certified clause outside the selected handler. Its captured segment and
  outside control come from the E6/E10 composition below. Clause-local
  requests are checked against the clause's own context; they do not silently
  pass through the removed handler.
- A request handled by an inner boundary, forwarded past this handler, or
  selected by a cell or native interpreter retains the corresponding
  conditional behavior. An outward request is not erased because `I` was
  removed from the static row.
- Non-return, abandonment, failure and unknown cases remain covered. Failure
  disposal is not assumed to complete as an ordinary return. Neither a listed
  may-case nor a row member asserts that the case executes.

The following rule constructs a finite handler cover from those already
certified inputs. `Cases_body` is the complete body cover at this handler
entry; its exposed requests already carry their local control and delimited
residuals. `Select_r` is a complete guarded nearest-selection cover for that
same request and actual context, including passing or outward alternatives.
`Cases_out` is the union of the guarded outcomes **produced** by the named
case rules, not a set of cases guessed from the effect row. An unknown case
can be included only with a covering upper bound that includes all relevant
outcomes and retains its obligations.

```sequent
J-Handle-Finite-Cover :=
  GAMMA; L, entry |- the certified B_body has finite complete cover Cases_body at this H
  for each normal return, failure, non-return or unknown in Cases_body, the applicable H-Return, H-Failure, H-Local-Divergence or covering H-Unknown case is established under its own guard
  for each request case r in Cases_body, Select_r is a certified complete nearest-selection cover for the same request and context
  for each source selection of this H in Select_r, H-Source-Capture and H-Select establish the matching actual clause entry or a covering failure or unknown
  for each such entered clause, its certified complete case cover is transformed by the applicable H-Clause outcome rules at the same subject delimiter
  for each pass, inner selection, builtin, excluded or outward alternative in Select_r, its applicable certified forwarding or interpreter case covers that same guard and residual
  every handler-entry, selection, return-transition and disposal failure is covered under its actual phase, or retained in a covering unknown
  every recursive or opaque residual uses its certified covering family or a covering unknown with its obligations
  Cases_out is the union of these produced cases with their correlated guards, local witnesses and obligations
  ===>
  GAMMA; L, entry |- HandleBehavior(B_body, B_i, I) has complete cover Cases_out
```

`H-Source-Capture`, `H-Select`, the clause outcome rules and `H-Forward` are
defined in the [behavior record](first-slice-behavior-coverage-rules.md#handler-composition).
The grouped return applies only to the newly composed subject delimited
immediately outside the **whole** group. If a physical group crosses the
smaller handler subject's delimiter, its final physical state is not a case
at that smaller delimiter. An established logical boundary interface or a
covering unknown is needed there; the enclosing group is composed separately.
No intermediate physical state or skipped continuation is invented. The rule joins facts from
the **same** request, selection and clause case. It does not pair a capture
from one branch with another branch's payload, invent a reply, or inspect
the body or clauses again. Ordinary clause typing, row and structural usage
remain independent of the possible reachability of a behavior case.

This is a sufficient finite construction conditional on its inputs, not a
proof that the present compiler emits the needed covers. A finite outer cover
does not by itself prove coverage of an unbounded residual; that residual
needs an established guarded certificate or the stated conservative fallback.
An unknown is not evidence that a program can pass the agreed no-error
admission. The universal property and representation of these covers require
separate system justification.

The clause's `k_i` is local and cannot be exported in a value or captured by a
nested function, recursive member, supplied method or nested clause. Those
barriers use established scope and no-capture facts; absence from an ordinary
value type is not such a fact. The handler and its clauses remain conditional
on their stated premises. `J-Handle-Finite-Cover` derives the composition only
when its selection, clause, failure and residual interfaces are established;
producing those complete interfaces in typed Core remains open.
[Handler entry and return](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
provide the operational correspondence to establish.

### Source-to-Core handler, capture and resume correspondence

An ordinary source handler lowers to an Effect Core handler with a body and
one clause record per operation. A source request or resume retains its own
checked operand as a child. The proposed correspondence below reuses those
child judgments and relates the **new** constructor and control step; it does
not check a body, clause or operand again. Private Store, registration and
hook associations are outside this case and retain their own contracts.

[Elaboration](../../../spec/elaboration.md) requires the exact effect,
operation, handler and resume-owner identities to survive in typed Core.
The current [`finish_handler`](../../../src/elaborate.rs#L14550) checks the
clauses, normalizes the resulting rows and constructs `HandlerNode`; each
[`EffectClause`](../../../src/core/effect.rs#L205) records its operation,
static resume identity and match arm. [`ResumeNode`](../../../src/core/effect.rs#L133)
stores the static handler and resume pair, `Consumed` use annotation and
operand child. Core [handler](../../../src/core/validate.rs#L16777) and
[resume validation](../../../src/core/validate.rs#L17059) currently check
their respective identities, clause contracts, operand/result types and rows.
Those implementation checks are evidence for this mapping, not evidence that
the proposed behavioral certificates are already carried by Core.

`Corr` below is an established relation between the source and Core cases:
it relates subjects, actual values, source and machine states, guards,
lexical instantiations, observations and scoped obligations. Renaming source
identities to Core identities alone does not equate source and machine states.
`H` and `u_i` are the static Core handler and clause resume identities;
`k` is a fresh **dynamic** clause activation introduced by one actual
selection. Repeated or recursive selections of the same static pair have
distinct dynamic owners. `ScopeObl` binds case-local pattern, owner and state
witnesses and preserves each obligation's original guard. Obligations of
ordinary clause typing and structural one-shot usage retain their own scope
and do not become conditional on a clause being reached at runtime.
`CaseObl(k,O)` instead attaches obligations to the **same already-bound**
dynamic case `k`; it does not bind a different owner or export `k` outside
its case. An enclosing composition scopes that witness when it leaves the
case. Handler-entry, body and outside obligations remain in their own scope,
not inside a clause-local binder merely because the handler has clauses.

```sequent
family handler-source-core-correspondence:
  J-Handler-Source-Core :=
    GAMMA |- source body : A ! epsilon_body ; B_body [O_body]
    the certified body correspondence supplies the same Core body child and a Corr-related behavior and obligations
    the exact source effect I and its complete operation contracts correspond to the Core instance I_core under the admitted substitution
    for each operation op_i, the certified pattern and clause correspondence supplies the same Core clause child under its own pattern bindings and static owner u_i
    for each clause, ordinary type, row and U(u_i,clause_i,available,consumed) are established independently of behavioral reachability
    the Core clause records retain op_i, u_i and that same checked pattern and child; H is the corresponding fresh static handler identity
    J-Handle-Composition and J-Handle-Finite-Cover, or their certified guarded alternatives, establish the new composition under outer obligations O_handle_outer and clause-local obligations O_handle_clause
    Corr relates the source handler entry, selection, clause, return, failure and residual cases to these same Core cases
    ===>
    GAMMA_core |- Handler(H,I_core,body_core,clauses_core) : A_core ! epsilon_out_core ; HandleBehavior_core [O_body_core union O_handle_outer union ScopeObl(clauses_core,O_clauses_core,O_handle_clause)]

  J-Selected-Capture-Source-Core :=
    GAMMA; L, phi |- Corr relates this source request and Core request, including the actual payload and each saved lexical instantiation
    GAMMA; L, phi |- the source selection and Core nearest-boundary contracts select the same corresponding handler activation and clause operation
    GAMMA; L, phi |- the same selected capture preparation and transfer succeed on both related cases
    GAMMA; L, phi |- Corr relates the selected segments, actual outside controls, payload bindings and their owner and completion obligations
    k is fresh for this dynamic selection and corresponds to this Core clause activation with static pair (H,u_i)
    GAMMA; L, phi |- the selected correspondence retains its applicable case obligations O_capture for this same k
    ===>
    GAMMA; L, phi |- correlated_selection_and_capture(source,Core,k) [CaseObl(k,O_capture)]

  J-Resume-Success-Source-Core :=
    GAMMA; L, phi |- correlated_selection_and_capture(source,Core,k) for static pair (H,u_i)
    GAMMA; L, phi |- the certified source and Core resume operand children have Corr-related cases and obligations O_operand
    GAMMA; L, phi |- ResumeNode(H,u_i,Consumed,operand_core) is within that clause's permitted lexical scope
    GAMMA; L, phi |- J-Resume-Composition holds for this same owner and operand, or retains its applicable obligations O_resume
    GAMMA; L, phi |- this actual normal operand case has related reply q and a live k in the correlated pre-restore states
    GAMMA; L, phi |- the corresponding source restore and Core restore both succeed for that same k, capture and outside continuation
    GAMMA; L, phi |- Corr relates their actual post-restore states, consumed k and restored control
    ===>
    GAMMA; L, phi |- correlated_successful_resume(source,Core,k,q) [CaseObl(k,O_operand union O_resume)]
```

These are conditional interfaces, not a proof that an arbitrary Core shape
has source provenance. Handler clause coverage, exact operation signatures,
least output row, pattern and one-shot checks remain ordinary admission
premises even if a behavioral case is unreachable. In `J-Handler-Source-Core`,
the body and clause correlations include all guarded request, return,
non-return, failure and unknown cases. A finite case construction can be used
only when its inputs establish complete coverage; otherwise the appropriate
guarded family or unknown and obligations remain. Clause-local witnesses are
not exported as free variables, and a closed use must establish every
applicable scoped obligation.

The successful selection rule relates a source step to an actual Core capture;
there is no source-lowering instruction that preallocates `k` or executes a
capture. A static `Consumed` annotation records structural use, not proof
that a runtime owner already exists or has been consumed. A resume operand
may request, fail, diverge or be abandoned before it returns: its existing
case contract covers those outcomes and no restore is invented for them.
Only a related normal operand case can apply the same-owner successful restore
relation; its source and Core request and handler frames use their own saved
lexical instantiations. This is not a complete resume cover. In particular,
Core restore can fail after taking the captured continuation or updating
accounting; those actual failure states must not be represented as a live
pre-restore owner or as the successful case. A complete source/Core resume
correlation must also cover operand request, non-return, abandonment and
failure, and all restore and disposal failures, including after-take cases,
or retain covering unknowns and their obligations. Neither effect rows
nor identical static sites prove exact selection or dynamic-owner identity.

The current validator reconstructs some facts from the assembled Core; this
schema does not establish equivalence to every such query. In particular,
the source/Core case relation and its coverage, the transport of obligations
and dynamic-owner witnesses through capture and restoration, and the
authenticated producer of delimited residual contracts remain to be proved.
Only after those obligations are discharged can a certified composition reuse
the resulting facts in place of a corresponding legacy query.

## Selection and owned capture: E6 and E10

Use the established `selects` judgments in the
[nearest-boundary record](first-slice-nearest-boundary-judgments.md#candidate-composition-rules):
selection follows ordered control from inside outward. Each request and
boundary is instantiated in its own saved lexical context. Exact effect
identity and complete arguments govern source-handler matching. If equality
is unsettled, retain both feasible matching and passing conditions; a failed
proof of equality is not a proof of inequality. Builtin cells and native or
outside-slice interpreters supply their own acceptance and authentication
facts. A frame passed during search remains in the crossed control; passing is
not closing it.

For a newly composed source-handler boundary `h` immediately inside an
already certified suffix `K`, the following rule derives its selection cover
without searching `K` again. The request and handler each retain their own
saved lexical instantiation. `I_r` and `I_h` are their actual complete
instantiated identities at this selection point, including all type
arguments. `lift_h` adds `h` to the front of a selected suffix's crossed
prefix, or to the front of an outward suffix's crossed prefix. It preserves
that suffix result's outside control and all its guarded obligations.
Here a successful-selection cover also permits `outward`: it means the search
reached the end of this certified context without an earlier internal failure,
not that an enclosing interpreter has already been found.

```sequent
J-Source-Distinct-Selection-Cover :=
  GAMMA; L, phi |- r is the same certified request case at the new context h :: K
  GAMMA; L, phi |- the actual h frame's handler descriptor resolves in the same executable program
  GAMMA; L, phi |- the actual request and h have established distinct declared effect identities
  GAMMA; L, phi |- the certified suffix K has complete successful-selection cover {(g_i, result_i) for each i} for this same r
  each result_i is an established selected or outward result with its own scoped guard and outside facts
  Cases = {(g_i, lift_h(result_i)) for each i}
  ===>
  GAMMA; L, phi |- Cases covers successful nearest selection of r in h :: K
```

This case passes `h` from the established distinct declared effect identities;
the current runtime need not instantiate that handler's arguments to decide
it. The request's own instantiation, any search or suffix failure and all
outside obligations remain separate. The following same-family rule is
conditional on successfully instantiating and comparing the complete
identities, and preserves both equality alternatives if they are not already
decided.

```sequent
J-Source-Boundary-Selection-Cover :=
  GAMMA; L, phi |- r is the same certified request case at the new context h :: K
  GAMMA; L, phi |- the actual h frame's handler descriptor resolves in the same executable program
  GAMMA; L, phi |- r and h have the same established declared effect identity
  GAMMA; L, phi |- this request's and h's saved instantiations successfully produce actual complete identities I_r and I_h
  GAMMA; L, phi |- the actual comparison required at h, if any, succeeds for those identities
  GAMMA; L, phi |- the equality and inequality guards for I_r and I_h cover this reached case
  GAMMA; L, phi, I_r != I_h |- the certified suffix K has complete successful-selection cover {(g_i, result_i) for each i} for this same r
  each result_i is an established selected or outward result with its own scoped guard and outside facts
  Cases = {(I_r = I_h, selected(h, [], K))} union {(I_r != I_h and g_i, lift_h(result_i)) for each i}
  ===>
  GAMMA; L, phi |- Cases covers successful nearest selection of r in h :: K
```

The equal branch uses `S-Here`; each unequal branch uses `S-Through` or
`S-Through-Outside` with the suffix's **existing** result. If arguments are
unresolved, both guards remain until the applicable facts
settle them. A branch is removed only by a proved contradiction. A finite or
recursive suffix cover remains conditional on its own coverage and scope; an
unknown suffix is not an empty one. Instantiation, equality comparison and
selection preparation can fail before successful selection, so the handler
behavior and no-error cover must retain those separate cases. The rule does
not prove that `r` occurs, that its payload crosses the selected prefix, or
that an interpreter replies.

The following candidate rule is one **conditional source selection**, not a
coverage proof. `phi` includes the correlated request, activation and selection
conditions. `prefix` is ordered from the request to the selected boundary;
`outside` is the remaining control. `crossing` requires the actual payload and
its dependencies to be admitted across each relevant owner in that prefix.
The fresh `k` belongs to this selection activation.

```sequent
J-Selected-Source :=
  GAMMA, phi |- certified_request(r, residual, local_control)
  GAMMA, phi |- selects(r, local_control ++ enclosing_control, selected(h, prefix, outside))
  GAMMA, phi |- payload_crossing(r, prefix) is established
  GAMMA, phi |- the selected clause contract of h accepts r's actual payload
  k is fresh for this clause activation
  GAMMA, phi |- the same source capture's preparation and transfer succeed, introducing k
  ===>
  GAMMA, phi |- source_selection(r, h, k, owned(prefix, h), outside, residual)
```

On this case the selected handler and crossed prefix move into the capture
owned by `k`; the clause receives the actual payload under its own saved
environment and runs outside that capture. The outside owners and their
completion obligations remain outside. The conclusion does not prove their
completion, safe discard, or a particular reply. Nested live clause captures
are owned recursively only where their own ownership facts establish that
relationship; non-owning handles do not confer ownership. A different
selection or repeated activation gets a fresh owner. This is the successful
case of the [source capture rule](first-slice-behavior-coverage-rules.md#select-a-source-handler-and-form-its-capture),
whose established transfer fact is reused here. Selection and payload
compatibility alone do not prove that preparation or transfer succeeds;
their failure cases remain in the behavior cover.

The [cell payload-crossing rule](first-slice-resource-rules.md#r4-actual-result-and-payload-crossing)
develops the in-slice resource part of the crossing premise; excluded owners
supply their own facts. Completeness of actual dependencies and production of
complete request and context contracts remain **unresolved**. The rule must be applied to every
feasible conditional source, builtin, native and outward alternative, and
unknown relevant behavior must remain covered or an obligation. The existing
[matching and coverage record](first-slice-matching-coverage.md) distinguishes
may-selection from an exact selection; a member of a may-set is not an exact
fact. `J-Selected-Source` neither selects a source handler unconditionally nor
supplies cell or native behavior. This rule is to be justified against
`E-Request-Select`, not run by inspecting the selected constituent again.

## Resume and structural usage: E7 and E9

Use the existing `U-Resume`, `U-Sequence`, `U-Match` and barrier obligations
in the [usage record](first-slice-continuation-use-trace.md#candidate-usage-judgments).
They describe a structural transition even on a path with no normal return;
therefore a proved empty normal-return cover does not license a second resume.
Every clause starts available and has structural outgoing state consumed.
A matching one-shot owner cannot change from consumed back to available.

For E7, let `k`'s certified capture contract give reply type `Q`, answer `A`,
handler output row `epsilon_out`, and a conditional `Restore_k(q, state, deps)`
behavior for the actual reply and resulting facts. The operand `v` is checked
once; `normal_fits` is the same relation used for binding and request operands.
The following candidate rule checks the new resume composition. `a` is a
fresh symbolic entry state for the same owner activation throughout the rule;
`entry_a(s0)` means `entry(s0) and s0 = a`. The post-operand state and reply
facts remain correlated with their covered case. Structural availability at
entry does not alone prove that the actual owner is live at operand return.

```sequent
J-Resume-Composition :=
  a is a fresh symbolic entry state; entry_a(s0) = entry(s0) and s0 = a
  GAMMA; k available, entry_a |- v : Q ! epsilon_v ; B_v(a)
  U(k, v, available, available)
  epsilon_v is included in epsilon_out
  GAMMA; k available, entry_a |- normal_fits(B_v(a), reply_premises_of(k,a))
  for every covered normal operand case, its correlated post-state establishes the same owner live and its reply and restore premises
  the restored behavior for each admissible case is established from k's capture contract
  ===>
  GAMMA; k available, entry_a |- resume v : A ! epsilon_out ; Seq(B_v(a), Restore_k), k consumed
```

One successful restore case can be constructed from the same selection's
certified capture and delimited port. Let `r` be the original selected
request, `C = K ++ [H]` its capture, and `O0` the outside recorded at
selection. `O_current` is the actual outside in the operand's **return**
state; it need not equal `O0`. `F` is this resume's actual pending clause
continuation. The restored segment ends at `H`, before `F` and any enclosing
clause suffix execute.

```sequent
J-Restore-From-Captured-Port :=
  GAMMA; L, entry |- selected_clause(r,H,payload,k,C,O0,bindings,clause_entry) is the original certified selection and C = K ++ [H]
  GAMMA; L, entry |- case(B_v, phi, z, return(q, state_q, deps_q)) for this actual resume operand
  GAMMA; L, entry, phi |- ClauseFact(state_q,k,H,C,O0,live) and CaptureFact(P,k,H,C,O0)
  GAMMA; L, entry, phi |- NearestOwner(state_q,k) and the actual pending control is RESUME(H,k) ++ F ++ CLAUSE(H,k,live(C)) ++ O_current
  GAMMA; L, entry, phi |- the actual q and deps_q satisfy this request's reply and applicable crossing premises
  GAMMA; L, entry, phi |- H-Restore-Control establishes the same successful restore to state_restored
  GAMMA; L, entry, phi |- the original request's certified Port_r(K,H,k,q,state_restored,deps_q) has complete behavior B_inner with its scoped obligations
  GAMMA; L, entry, phi |- the handler rules establish the complete conditional behavior B_restored = Handle_H(B_inner) up to the same pending F
  ===>
  GAMMA; L, entry, phi |- Restore_k(q,state_q,deps_q) = B_restored with k consumed and F pending at state_restored
```

`H-Restore-Control` and the port are the existing
[restore and port interfaces](first-slice-behavior-coverage-rules.md#restore-the-selected-segment).
If the successful restore physically merges consumed clause completions, its
certified logical expansion relates those actual frames without inventing an
intermediate machine state. The port is instantiated for the **same** actual
reply and post-restore state; an entire enclosing-expression residual is not a
replacement. The stated owner and pending-control facts describe the immediate
post-restore boundary; a later capture or abandonment may move or discard `F`
under its own rules. Any subsequent clause continuation is composed once after this
delimited behavior normally returns. Source and Core one-shot checking remains
independent of this case's reachability.

This derives `Restore_k` only for a covered normal operand return and
successful restore with those premises. Operand failure, request, no-reply,
non-return and restore failure retain their own cases. The capture contract
must still supply the matching live owner, its actual segment, local boundaries,
answer and reply relationships, and preservation of owners and outside
obligations. Missing `NearestOwner`, port, grouped-control, or boundary
assumptions remain scoped obligations rather than a reason to reopen the
operand, capture or clause. Operand
requests retain the pending resume; only a normal operand result can trigger
restoration. The actual reply and resulting state enter the captured segment;
its prior prefix is not replayed. Restoration consumes `k` once, reinstates the
selected handler and crossed control in their original order, and keeps the
clause continuation after that restored segment. The computation's eventual
answer and dependencies need not equal those of the reply. If the operand
does not return, the restore step does not occur through that frame. The
static structural `consumed` conclusion still applies for checking subsequent
syntax. `E-Resume-Operand` and `E-Resume-Restore` in the
[dynamic rules](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
are the separate operational obligations. Resume does not require discard
safety merely because a different clause could discard.

### A nested request's resumed operand

Consider `perform E.op (perform F.ask ())`, where the certified operation
contracts accept `F.ask : Unit -> P` and `E.op : P -> Q`. A surrounding source
handler `H_F` handles the inner request. This example leaves `P` and `Q`
opaque: only the established operand and operation interfaces are used. Let
`f_E = REQUEST(E.op, theta_E)` be the outer frame, with the instantiation
saved when the outer operand was entered. The following is one conditional
producer for the outer request, when the actual inner capture contains exactly
that frame and the selected handler.

```sequent
J-Nested-Perform-Reply :=
  GAMMA; L, entry, phi |- the certified operation contracts accept F.ask : Unit -> P and E.op : P -> Q
  GAMMA; L, entry, phi |- entry of the outer perform established f_E = REQUEST(E.op, theta_E) before evaluating its operand
  GAMMA; L, entry, phi |- selected_clause(r_F,H_F,(),j,C,O0,bindings,clause_entry) and C = [f_E,H_F] for the actual inner request
  GAMMA; L, entry, phi |- the operand of the actual resume of j returns reply q : P with dependencies D_q in state_q, satisfying the reply and crossing premises
  GAMMA; L, entry, phi |- the same successful H-Restore-Control transition restores C from state_q to state_restored, with j consumed
  GAMMA; L, entry, phi |- the outer request-frame transition reached from state_restored passes its applicable preparation and request-formation checks
  ===>
  GAMMA; L, entry, phi |- the resumed operand introduces request(r_E, [], R_id), where r_E is E.op instantiated using theta_E with actual payload q and dependencies D_q
```

The derivation uses `Port-Empty` at `f_E`: after restoration the actual reply
reaches that frame unchanged, without executing the handler boundary or the
clause continuation. `Frame-Perform` then constructs the request from that
reply and the frame's saved instantiation. The precondition on request
formation retains its actual failure alternatives. This is a logical request
phase: the evaluator pops the request frame and enters `return_request`,
which checks disposal, instantiates the effect and continues interpreter
selection; the rule does not require a separately observable machine state at
that phase. The actual surrounding control and ownership facts are those
carried by the successful restore and request transitions, including any
certified logical expansion of grouped clause frames.

The inner selection establishes neither an interpreter for `r_E` nor its
reply. For example, if `r_E` has the exact effect instance of `H_F`, the
reinstalled handler can be the nearest source handler for this *new* request;
the nearest-boundary, crossing and capture rules must establish that selection
and any successful clause entry for the actual case. Its new dynamic owner is
fresh even if static handler identities coincide. A different interpreter,
failure, no reply, discard and non-return remain their own covered cases.
This producer composes the already certified selection, restore, empty port
and frame contracts; it does not check the inner operand or handler again. The
corresponding operational sequence is `E-Perform-Operand`, request selection
and `E-Resume-Restore` in the
[dynamic semantics](../../../spec/dynamic-semantics.md#effect-handlers-and-completion).

## Discard and close: E8

The [discard ownership trace](first-slice-discard-ownership-trace.md#candidate-judgments-and-discard-rule)
distinguishes the one-shot consumption from the owned close. For one possible
selected capability and capture, write `plan` for a certified structural
close plan: it contains precisely owned closing obligations in their specified
order. A live nested clause contributes its own certified capture plan at its
structural position; a consumed clause contributes no additional capture.
An association without ownership contributes no authority. Plans for opaque
constituents must be supplied by their established interfaces rather than
reconstructed by traversing those constituents.

For ordinary discard, use the single
[owned-discard rule](first-slice-close-rules.md#dependencies-and-the-discard-composition).
It requires a cover of every possible selected capture and, under each case's
own guard, establishes its plan, outside completion, interpretation and
dependency premises. Its close row combines the requirements of all covered
plans. The result retains the appropriate guarded plan and outside context for
each case. This is the E8 rule as well; applying another rule to recompute the
same discard facts would repeat the work.

The remaining derivations for those premises are required here as well. In
particular, an owner
being outside the plan does not prove its scheduled completion remains
reachable. A running cleanup or unfinished close cannot be abandoned. An
armed owned cleanup may be scheduled in order; an outer handler with the same
instance cannot replace a removed nearest required interpreter. Surviving
source handlers discharge appropriate residual effects at their own boundaries.
Resource, cleanup, backing and external facts enter through their own certified
contracts. An unproved relevant ownership, completion, interpretation or row
premise leaves an obligation and cannot grant discard; an unknown relevant
callee may prevent this proof without prohibiting resource-free resume.

The type rule schedules owned closing before the surviving clause continues;
it does not assert that actions have already run or terminate. On successful
`E-Discard`, the owner is consumed and the owned close is scheduled. If that
closing control completes successfully, its owned obligations have closed;
abandoned suffixes are not replayed. Initial preparation failure occurs before
consumption; later internal failure may follow already performed effects.
Neither this rule nor its named premises proves those failures unreachable.
The corresponding behavior and failure steps are in
[effect handlers and completion](../../../spec/dynamic-semantics.md#effect-handlers-and-completion).

## Control facts for malformed-handler checks

The following candidate facts connect the preceding judgments to individual
malformed-control branches in the [handler failure
table](first-slice-failure-judgments.md#source-handler-request-resume-and-discard-cases).
They describe the same actual request, executable program, owner activation,
control position and phase in each guarded case. They are not a new scan of a
checked fragment, a representation of Core, or an overall soundness proof.
Each producer establishes its part while checking the new constructor; later
uses instantiate that certificate. An opaque control or callable boundary
supplies its established descriptor, ownership and behavior interface, or
retains an explicit obligation. Store, registration, region, native and network
control remain outside this slice.

### Declarations and actual request selection

Let `Descriptor(P, n, kind, x)` assert that node `n` in the same immutable
executable program `P` has the stated admitted request or handler descriptor
`x`. It is an authenticated projection of the checked Core judgment, not an
assertion that a node number is globally meaningful. A request descriptor
records the declared operation and Core instance expression; a handler
descriptor records its static handler identity, Core instance expression and
certified operation clauses. Neither descriptor fixes a runtime lexical
instantiation or environment. A particular entry creates those dynamic facts:
`RequestFrame` retains the actual request instantiation saved before its
operand, and `HandlerFrame` retains the actual handler entry environment and
its instantiation. Different recursive entries of the same node can carry
different saved contexts. The request fact at selection retains its own entry
and operand-return correlation even though the physical request frame has
already been popped. A clause contract also needs its admitted pattern and
the ordinary value/heap facts that make matching the actual payload valid;
ordinary type `D` alone does not prove alias resolution, storage or work
succeeds.

```sequent
family handler-descriptor-facts:
  J-Request-Descriptor :=
    GAMMA |- J-Operation-Instance authenticates declared operation op and its conditional signature
    GAMMA |- the checked Core constructor n in P is this request with Core instance expression I_r
    ===>
    GAMMA |- Descriptor(P, n, request, (op, I_r))

  J-Handler-Descriptor :=
    GAMMA |- J-Handle-Composition authenticates handler h and its exact clause contracts
    GAMMA |- the checked Core constructor n in P is this handler with Core instance expression I_h
    ===>
    GAMMA |- Descriptor(P, n, handler, (h, I_h))

  J-Request-Frame :=
    GAMMA, phi |- Descriptor(P, n, request, (op, I_r))
    GAMMA, phi |- this actual entry has lexical instantiation theta_r
    GAMMA, phi |- successful perform entry installs its pending request frame at s'
    ===>
    GAMMA, phi |- RequestFrame(s', P, n, op, I_r, theta_r)

  J-Handler-Frame :=
    GAMMA, phi |- Descriptor(P, n, handler, (h, I_h))
    GAMMA, phi |- this actual entry has environment E_h and lexical instantiation theta_h
    GAMMA, phi |- successful handler entry installs its boundary at s'
    ===>
    GAMMA, phi |- HandlerFrame(s', P, n, h, I_h, E_h, theta_h)

  J-Selected-Clause-Descriptor :=
    GAMMA, phi |- RequestFrame(s_entry, P, n_r, op, I_r, theta_r)
    GAMMA, phi |- the actual request r at s follows that same frame and its operand's normal return
    GAMMA, phi |- HandlerFrame(s, P, n_h, h, I_h, E_h, theta_h) is the actual active boundary
    GAMMA, phi |- exact nearest selection for r at s chooses that same dynamic handler frame in P
    GAMMA, phi |- instantiate(I_r, theta_r) = instantiate(I_h, theta_h)
    GAMMA, phi |- h's certified clauses cover op
    ===>
    GAMMA, phi |- the source request and selected-handler descriptors resolve and h has the matching clause

  J-Selected-Pattern-Match :=
    GAMMA, phi |- the same selected clause has certified irrefutable pattern p for operation input D
    GAMMA, phi |- the actual payload and current heap satisfy the ordinary representation contract for D
    GAMMA, phi |- the established pattern correspondence applies to this p, payload and heap
    ===>
    GAMMA, phi |- this clause cannot fail the impossible-match check
```

These conclusions exclude the corresponding wrong-node, wrong-kind and missing
source-clause branches only in the stated case. The conditional frame facts are
introduced at entry and preserved across the actual operand and control
transitions by their established contracts; the static node does not determine
their dynamic context. Selection must also carry
valid descriptors for every actual boundary it encounters; a passed opaque
boundary supplies its own interface. A possible candidate in a may-set is not
an exact nearest selection. Outward requests require their eventual interpreter
contract; an unknown suffix or an effect-row member does not establish one.
The runtime's [request and search](../../../src/eval/machine.rs#L4440) and
[selected-clause lookup](../../../src/eval/machine.rs#L4654) are evidence for
the separate checks. Failed instantiation, pattern storage, pending disposal
and work or reservation exhaustion remain separately covered failure cases.

### Clause owner, captured segment and accounting

Write `ClauseFact(s, k, h, C, O0, phase)` for one dynamic clause activation
`k`, its selected handler `h`, actual capture `C`, selection-time outside
control provenance `O0`, and live or consumed phase at state `s`. `O0` records
what was outside the capture when `k` was created; it does not claim that the
same control is still active or unchanged at `s`. The actual current placement
and outside control and obligations are separately indexed by `s` and supplied
by the applicable control contract. The static `(handler, owner)` identifiers
in Core are not themselves a dynamic activation: recursion can create more
than one clause with the same pair. `NearestOwner(s, k)` additionally means
that the runtime's innermost lookup for this pair reaches this **same** clause
and not a nearer consumed or different activation. `U(k, e, available,
consumed)` alone is a structural use fact; it neither identifies the runtime
clause nor proves this nearest-owner fact.

`CaptureFact(P, k, h, C, O0)` records that the same live `k` owns exactly one
ordered segment through its selected handler, with selection-time outside `O0`
excluded. It preserves that provenance without equating `O0` to the current
outside control. Its
logical control order is `prefix ++ [h]`; in the current frame-vector
representation the selected handler is the first physical frame of that
capture. It contains the established descriptor contracts of its frames and
the recursively owned nested-capture interfaces, with their actual phases and
associations. It carries those contracts as a compositional summary; a later
resume or discard does not traverse the segment to establish them again.
The summary may be conditional and must cover every possible captured case.

```sequent
family selected-owner-facts:
  J-Introduce-Selected-Owner :=
    GAMMA, phi |- J-Selected-Source and H-Source-Capture establish the same r, h, k, C and O
    GAMMA, phi |- the selected descriptor and crossed-control certificates apply to this actual case in P
    GAMMA, phi |- successful capture moves C once and installs this fresh live clause at s'
    ===>
    GAMMA, phi |- ClauseFact(s', k, h, C, O, live) and CaptureFact(P, k, h, C, O)

  J-Preserve-Clause-Owner :=
    GAMMA, phi |- ClauseFact(s, k, h, C, O0, live) and CaptureFact(P, k, h, C, O0)
    GAMMA, phi |- a certified intervening transition takes s to s' without consuming k
    GAMMA, phi |- that transition preserves this owner's capture, descriptor and phase
    GAMMA, phi |- its certified state relation maps the actual placement and outside obligations at s to those at s'
    ===>
    GAMMA, phi |- ClauseFact(s', k, h, C, O0, live) and CaptureFact(P, k, h, C, O0)
```

`J-Introduce-Selected-Owner` uses the one selection and capture already
established by the behavior rules; it does not perform another selection.
`J-Preserve-Clause-Owner` applies only when the actual transition's interface
preserves those facts. An outward request can move the clause and its capture
inside another owned capture, so its actual location may change. A successful
restore moves that same owner back in its recorded phase; abandonment may
instead close it under its own obligations. A failed or nonreturning operand
does not imply that control returns to a pending resume.

#### Preserve an owner across a resume operand

A resume first evaluates its operand with a new pending resume frame. The
following rules introduce and transport the facts needed for that frame.
`PendingResume(s,f,k)` names this actual frame and dynamic owner, not just a
static source occurrence. `O0` remains the selection-time provenance of `k`;
the current outside control is supplied by the state relation in each case.
The successful frame entry below does not consume `k`.

```sequent
family resume-operand-owner:
  J-Resume-Operand-Owner :=
    GAMMA, phi |- ClauseFact(s, k, h, C, O0, live) and CaptureFact(P, k, h, C, O0)
    GAMMA, phi |- NearestOwner(s, k) for this resume node's static pair
    GAMMA, phi |- successful resume-operand entry pushes f and begins the certified operand from s'
    ===>
    GAMMA, phi |- ClauseFact(s', k, h, C, O0, live) and PendingResume(s', f, k)

  J-Operand-Selection-Owner :=
    GAMMA, phi |- ClauseFact(s, k, h, C, O0, live) and CaptureFact(P, k, h, C, O0)
    GAMMA, phi |- PendingResume(s, f, k) for the operand's actual pending frame
    GAMMA, phi |- r_j is this operand's certified actual request case
    GAMMA, phi |- selected_clause(r_j, h_j, payload_j, j, C_j, O_j, bindings_j, entry_j) is the same successful source selection
    GAMMA, phi |- j is fresh for that selection and differs from the already live dynamic owner k
    GAMMA, phi |- the exact selection interface places each of f and k either inside C_j or in O_j
    GAMMA, phi |- this successful selection takes s to s', moves the captured positions once and preserves the outside positions
    ===>
    GAMMA, phi |- ClauseFact(s', k, h, C, O0, live) and PendingResume(s', f, k) at those same moved or outside positions

  J-Operand-Resume-Owner :=
    GAMMA, phi |- r_j is this operand's certified request case and selected_clause(r_j, h_j, payload_j, j, C_j, O_j, bindings_j, entry_j) records its actual source selection
    GAMMA, phi |- j was fresh for that selection and differs from the original dynamic owner k
    GAMMA, phi |- the same live j owns C_j and an actual reply resumes j successfully from s to s'
    GAMMA, phi |- ClauseFact(s, k, h, C, O0, live) and CaptureFact(P, k, h, C, O0)
    GAMMA, phi |- PendingResume(s, f, k) remains at its certified captured or outside position
    GAMMA, phi |- the certified selection and clause interfaces locate f and k in C_j or in the surviving outside control
    GAMMA, phi |- the successful restore moves the captured positions back in order and the clause contract preserves any relevant outside position
    ===>
    GAMMA, phi |- ClauseFact(s', k, h, C, O0, live) and CaptureFact(P, k, h, C, O0) and PendingResume(s', f, k) at the established restored or outside positions
```

In `J-Operand-Selection-Owner`, `s'` is the post-selection state supplied by
that successful transition, and `j` is fresh for that selection. The same
request and selection witness is retained as historical provenance for
`J-Operand-Resume-Owner`; its entry and outside facts are not silently treated
as the later restore state. The dynamic owners `j` and `k` differ even when
their static handler/owner pairs coincide. `f` and `k`
need not move together: an inner handler can capture `f` while leaving `k`
outside, or an outer selection can capture the clause too. Neither case makes
`k` active or nearest merely by preserving its logical owner fact. A selected
clause with the same static pair may shadow it; a consumed nearer clause may
also block lookup. A selected clause can discard instead of resume, or can
diverge: use that case's own close, clause and outside-completion contracts.
The restore rule is conditional on an actual successful reply and on the
surviving outside interface; it does not assume the original outside control
`O0` has stayed unchanged or turn a no-reply case into a reply.

On an actual normal operand return, the certified operand case must supply the
same pending frame and the actual active prefix above `k`. Once that prefix's
`NoClauseKey` contract is established, `J-Nearest-Revealed` below establishes
the dynamic nearest owner in that return state. The reply, capture and
restoration checks then use that **same** return case. If the operand returns
with the pending frame abandoned, a different owner nearest, an unknown
prefix, or a missing outside-preservation fact, those premises remain
unproved; the type checker cannot recover them from the operand's ordinary
result type or rerun its body. The operand's structural usage judgment remains
independent of normal-return reachability.

The nearest-owner fact has its own elementary producers. `key(k)` denotes the
static handler/owner pair associated with this particular dynamic clause; it is
not the dynamic identity of `k`. `f` is one newly composed active frame.

```sequent
family nearest-dynamic-owner:
  J-Nearest-New-Clause :=
    GAMMA, phi |- J-Introduce-Selected-Owner establishes the new active clause k at s'
    GAMMA, phi |- the new clause is innermost in the actual post-selection control
    ===>
    GAMMA, phi |- NearestOwner(s', k)

  J-Nearest-Pass-Frame :=
    GAMMA, phi |- NearestOwner(s, k)
    GAMMA, phi |- a successful control transition pushes exactly f above k and takes s to s'
    GAMMA, phi |- f is not a clause with static pair key(k)
    ===>
    GAMMA, phi |- NearestOwner(s', k)
```

If a newly active clause has the same static pair, the second rule does not
apply to the older activation. Its completion, capture or abandonment must be
accounted for before a later use can establish that the older clause is again
nearest. An operand certificate can supply the needed relationship for each
normal result; a nonreturning or abandoned operand does not manufacture that
result. A capture or restore supplies its actual ordered-control relationship
from its own established interface rather than assuming that all owners stay
at their former active positions.

The following interface derives the nearest-owner fact when a newly composed
active prefix is known not to contain a competing clause with the same static
pair. `NoClauseKey(F,key)` covers the **active** frames in `F`; it is not a
claim that no nested capture owns such a clause. It excludes both live and
consumed clause frames with that pair, because the runtime's lookup encounters
either before it can reach an older owner. Each atomic-frame judgment is
established when that frame is introduced; a certified opaque prefix supplies
the corresponding fact or leaves an obligation.

```sequent
family derive-nearest-from-prefix:
  J-No-Clause-Key-Empty :=
    ===>
    GAMMA, phi |- NoClauseKey([], key)

  J-No-Clause-Key-Frame :=
    GAMMA, phi |- the newly formed active frame f is not a clause or its established static pair differs from key
    ===>
    GAMMA, phi |- NoClauseKey([f], key)

  J-No-Clause-Key-Join :=
    GAMMA, phi |- NoClauseKey(F_1, key) and NoClauseKey(F_2, key)
    GAMMA, phi |- the new active prefix is exactly F_1 ++ F_2 with both certified interfaces preserved
    ===>
    GAMMA, phi |- NoClauseKey(F_1 ++ F_2, key)

  J-Nearest-Revealed :=
    GAMMA, phi |- the actual active control at s is prefix ++ [clause(k)] ++ outside
    GAMMA, phi |- ClauseFact(s, k, h, C, O0, live) and key(k) = key
    GAMMA, phi |- NoClauseKey(prefix, key)
    ===>
    GAMMA, phi |- NearestOwner(s, k)
```

For example, when a newer same-pair clause finishes and its boundary is
removed, its certified successor control may expose an older live `k`. The
older clause becomes nearest only if the resulting active prefix has the
required `NoClauseKey` fact; a still-present consumed clause with that pair
prevents the conclusion. A capture or restore can instead move frames into or
out of the active prefix. Its established control transition must supply the
corresponding prefix and guard before this rule applies. The join uses each
certified prefix once, and a use of `NearestOwner` does not scan it again.
An unknown frame or a conditional pair equality is covered by guarded cases or
an obligation; an absent proof of equality is not inequality. These rules
are sufficient for the identified prefix case, not a claim that every
recursive or opaque case already publishes the required interface.

Descriptor coverage can also be assembled at the new boundary. `DescCover(P,
C)` states that every handler frame physically present in the root segment
`C` has a descriptor resolved in `P`. For a new segment, its checked frame
contract supplies either that fact for a handler frame or that the frame is
not a handler; concatenating disjoint certified segments preserves both
covers. A frame that owns a nested capture carries its nested capture's own
cover independently. The current resume loop checks handler descriptors in
the root segment; discard's nested inspection requires the covers of the
actual nested segments as well. Unknown frames need their applicable opaque
contract. This construction consumes frame and segment certificates once; it
does not inspect a certified segment's frame list at a later resume.

The root and recursively owned covers are distinct. `DeepDescCover(P,C)`
includes the root cover and the independently certified deep cover for each
ordinary nested clause capture in this **new** component. A non-handler frame
does not contribute a root handler descriptor; if it owns nested control,
that control still needs its own deep interface. An excluded frame supplies
its applicable deep interface under its boundary contract. The following
rules form those interfaces from already checked constituent facts.

```sequent
family capture-descriptor-coverage:
  J-Descriptor-Empty :=
    ===>
    GAMMA, phi |- DescCover(P, []) and DeepDescCover(P, [])

  J-Descriptor-Handler :=
    GAMMA, phi |- f is exactly the new handler frame with node n and handler h in P
    GAMMA, phi |- Descriptor(P, n, handler, (h, I_h))
    ===>
    GAMMA, phi |- DescCover(P, [f]) and DeepDescCover(P, [f])

  J-Descriptor-Plain :=
    GAMMA, phi |- f is exactly a new non-handler frame with no owned nested control
    ===>
    GAMMA, phi |- DescCover(P, [f]) and DeepDescCover(P, [f])

  J-Descriptor-Nested-Clause :=
    GAMMA, phi |- f is exactly a new ordinary clause frame owning C_inner
    GAMMA, phi |- DeepDescCover(P, C_inner) is its established nested capture interface
    ===>
    GAMMA, phi |- DescCover(P, [f]) and DeepDescCover(P, [f])

  J-Descriptor-Join :=
    GAMMA, phi |- the new segment C is exactly the ordered disjoint composition C_1 ++ C_2
    GAMMA, phi |- DescCover(P, C_1) and DescCover(P, C_2)
    GAMMA, phi |- DeepDescCover(P, C_1) and DeepDescCover(P, C_2)
    ===>
    GAMMA, phi |- DescCover(P, C) and DeepDescCover(P, C)
```

Each rule's program `P` is the same executable program used by the eventual
descriptor lookup. The nested rule neither makes the nested frames part of
the root resume scan nor infers their descriptors from the outer clause's
node. For an unknown owner or excluded boundary, its applicable certified
deep interface is required; `J-Descriptor-Plain` cannot erase it. The
source-selection frame and every newly joined prefix contribute their
established descriptors, so the captured root cover can be retained with that
capture. The post-take resume lookup uses its root cover; discard's recursive
inspection uses the corresponding nested covers and separately authenticated
owner and selected-cut facts. Descriptor coverage is not enough to prove work,
reservation, pattern or disposal safety.

The captured-frame ledger needs a separate invariant from ordinary one-shot
usage and from cell-owner accounting. Let `Segments(s)` describe every
counted physical captured segment owned by this machine, including nested
segments and contributions supplied by excluded-owner contracts, with each
segment counted exactly once. `CaptureCountInv(s)` states that the machine's
`captured_cells` equals the sum of their physical lengths and that ownership
of these segments is disjoint. It is initialized by the machine-entry
contract or supplied by an opaque enclosing context. The set is a logical
description, not a request to build a runtime registry or repeatedly inspect
control.

```sequent
family captured-frame-accounting:
  J-Account-New-Capture :=
    GAMMA, phi |- CaptureCountInv(s) and the actual selected suffix has physical length l
    GAMMA, phi |- successful source capture moves this suffix once to new owner k at s'
    GAMMA, phi |- its nested captured segments remain separately counted and no outside segment is duplicated
    ===>
    GAMMA, phi |- CaptureCountInv(s') and captured_cells(s') = captured_cells(s) + l

  J-Resume-Capture-Count :=
    GAMMA, phi |- CaptureCountInv(s) and ClauseFact(s, k, h, C, O, live)
    GAMMA, phi |- C is the same counted root segment and its physical length is l
    ===>
    GAMMA, phi |- l <= captured_cells(s), so the resume accounting subtraction is defined

  J-Discard-Capture-Count :=
    GAMMA, phi |- CaptureCountInv(s) and ClauseFact(s, k, h, C, O, live)
    GAMMA, phi |- the discard contract identifies exactly the disjoint counted segments it inspects and their total length q
    ===>
    GAMMA, phi |- q <= captured_cells(s), so the discard accounting subtraction is defined

  J-Account-Resume :=
    GAMMA, phi |- CaptureCountInv(s) and ClauseFact(s, k, h, C, O0, live)
    GAMMA, phi |- C is the same counted root segment of physical length l, with its nested captures separately counted
    GAMMA, phi |- successful resume takes s to s', moves C to active control once, and preserves all other counted segments
    ===>
    GAMMA, phi |- CaptureCountInv(s') and captured_cells(s') = captured_cells(s) - l

  J-Account-Discard :=
    GAMMA, phi |- CaptureCountInv(s) and ClauseFact(s, k, h, C, O0, live)
    GAMMA, phi |- the admitted discard interface identifies exactly its disjoint root and recursively owned segments with total length q
    GAMMA, phi |- preflight succeeds and the subsequent successful transfer takes s to s', removes those counted segments and preserves all others
    ===>
    GAMMA, phi |- CaptureCountInv(s') and captured_cells(s') = captured_cells(s) - q
```

On successful resume, only the root segment's length `l` is subtracted;
already-owned nested captures remain counted when they move back inside the
restored frames. On successful discard, `q` includes precisely the nested
segments traversed by that discard's admitted close contract; an excluded
owner's internal segments contribute according to its own interface and are
not silently equated with the traversed set. For disjoint segments already
counted in a representable ledger, every nonnegative partial sum used to form
`q` is bounded by that ledger, excluding that sum's overflow. Capture quota,
physical reservation and work failures require the separate numerical
exclusions; positive accounting does not prove those operations succeed.

The two post-state rules apply only to the successful **whole transfer**.
They do not assert that a failed restore rolls back: the current resume trace
loop can fail after taking the capture but before decrementing the ledger.
Discard preflight failure occurs before its transfer and supplies its own
unchanged-accounting case. A successful discard consumes nested live clause
tickets during transfer, while scheduling their owned close positions in
structural order; it does not subtract a nested captured segment a second
time when the close cursor later reaches that position. Those distinctions
are specified in the [failure cases](first-slice-failure-judgments.md#source-handler-request-resume-and-discard-cases)
and [nested close plan](first-slice-close-derivation-rules.md#compose-an-owned-plan).

### Resume and discard checks

For an ordinary resume or discard, the current runtime first looks up the
innermost clause with the static pair. It requires a live capture and
`completion_count = 1` for that selected owner. Consumed ordinary clause
boundaries can have a larger positive count when the implementation has merged
adjacent equivalent completions; their representation must not be incorrectly
treated as another live capability. Other owner kinds and their association
checks are imported from their own interfaces.

```sequent
family handler-control-exclusions:
  J-Live-One-Shot-Lookup :=
    GAMMA, phi |- ClauseFact(s, k, h, C, O, live) and CaptureFact(P, k, h, C, O)
    GAMMA, phi |- NearestOwner(s, k) for the actual resume or discard node's static pair
    GAMMA, phi |- the checked ordinary owner representation has one live capture and completion_count = 1
    ===>
    GAMMA, phi |- this lookup selects k with its live C and passes its live/count checks

  J-Discard-Shape :=
    GAMMA, phi |- ClauseFact(s, k, h, C, O, live) and CaptureFact(P, k, h, C, O)
    GAMMA, phi |- the applicable owned-discard judgment admits this exact C and its nested close plan
    GAMMA, phi |- no forbidden running or unfinished completion belongs to that owned closure
    GAMMA, phi |- each nested clause has a positive count and every live or associated clause has count 1
    GAMMA, phi |- each nested selected cut and inspected handler descriptor has its certified matching identity
    GAMMA, phi |- each inspected excluded-owner association matches an owner in this closure under its own contract
    ===>
    GAMMA, phi |- the inspected capture has no forbidden unfinished completion or malformed nested clause for this discard
```

The first rule consumes the runtime-position fact together with the existing
structural usage proof. The descriptor cover is produced from the checked
frame interfaces at capture formation and preserved by capture transfer;
it supplies the premises of the existing
[failure exclusion](first-slice-failure-judgments.md#source-handler-request-resume-and-discard-cases)
for that same root segment. Reuse that result instead of checking its frames
again. In particular,
the current [resume implementation](../../../src/eval/machine.rs#L5208) can
fail a handler-descriptor lookup after taking the capture and before updating
accounting. The valid descriptor fact excludes that branch; if it is missing,
the failure case must retain the already-taken state and possible disposal.

`J-Discard-Shape` consumes the already certified close plan and its structural
positions, including nested live clauses and their selected-handler facts. A
running cleanup or unfinished close in the abandoned closure cannot satisfy
the discard premise, even if the one-shot use itself is valid. A captured
registration association must refer to an owner admitted by the excluded
registration contract for the same captured closure; mismatched association is
a separate runtime invalid-control case. The current
[`selected_handler_for_discard`](../../../src/eval/machine.rs#L1041) does not
by itself reject an absent first handler; the stronger shape above comes from
source selection and its preserved certificate, not from that runtime test.
Preflight failure leaves the capture owned and its accounting unchanged; a
successful discard consumes it and schedules the certified close without
claiming that close actions terminate.

The outstanding work is to establish `NearestOwner` from the source and Core
scope/usage rules for recursive activations and operand requests; prove that
the descriptor and frame interfaces survive every applicable opaque boundary;
derive the disjoint ledger and nested-plan correspondence for every in-slice
constructor and supplied outside contract; and connect ordinary payload and
heap representations to pattern checks. These schemas do not yet show that
the present verifier can be removed or that work, quota, allocation,
instantiation and disposal failure guards are impossible. The global
preservation argument is a system soundness proof, separate from checking any
particular certified fragment.

## Existing producers, consumers and remaining work

| Families | Current producer or consumer | Candidate disposition and remaining gap |
| --- | --- | --- |
| E1–E3 | [Effect and row rules](../../../spec/static-semantics.md#effects), [row formation](../../../spec/static-semantics.md#computation-types-and-effect-rows) and [Core validation](../../../src/core/validate.rs#L18808) authenticate declarations and operation identities. | Reuse checked identities, kinds, types and constraints. Correspondence of retained source and Core facts and all row consumers remains to be audited. |
| E4–E6, E10 | [Request elaboration](../../../src/elaborate.rs#L13966), [handler clause checking](../../../src/elaborate.rs#L14798), and [selection analysis](../../../src/core/capture/control.rs#L5966) establish or consume different request, context and clause facts. | The certified case and nearest-selection interfaces must cover the same consumers, including contextual and unknown cases. Their representation, crossing and coverage proofs remain open. |
| E7–E9 | [Source usage](../../../src/elaborate.rs#L30759), [Core usage and scope](../../../src/core/validate.rs#L12552), and [completion selection](../../../src/core/capture/control.rs#L7181) check distinct inputs and results. | Compose established usage, capture, restore and close facts. Full source-to-Core correspondence, no-capture boundary facts, recursive owned-close derivation, surviving completion and interpreter/row premises remain open. |
| All | [Core capture validation](../../../src/core/validate.rs#L13803) reconstructs relationships where its gate applies; shared analyses also serve outside-slice consumers. | Current validation and shared consumers remain in force. No existing check is shown removable here. Reconcile certified reuse with [AD-0007](../../decisions/AD-0007-typed-core-dialects.md) before changing that boundary. |

The rules expose the needed introductions and compositions; they do not yet
establish a complete or checkable representation, all case coverage, all
producer and consumer dispositions, or operational soundness. Separate
system-level proofs must connect the judgments to the operational steps and
the first slice's narrow correctness target under its stated environmental and
outside-slice assumptions. Current tests and traces are evidence for bounded
cases, not those proofs. This record does not authorize implementation or a
change to current semantics.
