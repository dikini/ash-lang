# First Slice: Nearest-Boundary Judgments

This record refines `nearest_source` and the selection cases in the
[request and capture judgment](first-slice-request-capture-judgments.md#select-a-source-handler).
It proposes how type-system facts can account for nearest-boundary selection
without rechecking a certified request or context. It is not a complete
calculus, a checking algorithm or current Ash semantics. The
[specification](../../../spec/README.md) states current behavior.

## The fact to establish

For a particular possible request, a selection judgment must identify every
relevant boundary that could be the **nearest accepting boundary**, together
with the control crossed to reach it and the context outside it. It must also
account for a request that passes all known boundaries and remains outward.
On successful runtime selection, a request selects one nearest accepting
boundary; an unhandled request has no selected boundary. Static typing may
need multiple conditional cases because the request's type arguments, target
or even precise behavior are not yet known.

The judgment is derived from certified request and context contracts. The
context at a request includes control inside the opaque computation as well as
the enclosing composition, as specified in the
[request/capture record](first-slice-request-capture-judgments.md#candidate-composition-rules).
It must preserve the order, owner, phase and completion facts of crossed
control. A boundary passed during selection is not thereby discarded or
closed: if a source handler is selected farther out, the crossed control is
part of the selected capture.

## Existing verification

Current [label specialization](../../../src/core/capture/control.rs#L2712)
substitutes request and boundary arguments in their respective saved contexts.
[Label matching](../../../src/core/capture/control.rs#L2813) returns two
possibilities: whether this candidate can be selected and whether the request
can continue outward. A definite exact match selects without crossing that
candidate; a definite mismatch crosses it; an uncertain match can do either.
Different effect identities cannot match. Unproved generic arguments do not
establish inequality, and an applicable, established row-tail lacks fact can
exclude a candidate from that tail.

[Boundary discovery](../../../src/core/capture/control.rs#L5966) combines
those possibilities with the control context. For builtin cells it compares
possible abstract operand targets with resource occurrences and owners; it
has separate handling for other interpreter kinds. It follows each possible
selected boundary and any possible outward
route. Its [consumers](../../../src/core/capture/control.rs#L6156) then check
the selected payload, source clause, builtin or other interpreter, or escaped
request. Selection alone does not prove safe payload crossing, safe discard or
successful cleanup. Unknown higher-order calls may return normally or request
repeatedly; an unknown possibility is not itself evidence of absence.

The [runtime request step](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
instead uses the actual saved instantiations and ordered runtime control to
select a single nearest accepting boundary. These traces explain the checks;
they do not prove their complete correspondence or show that current analysis
can be removed. In particular, the analysis graph is not already a complete
typed certificate.

## Candidate selection facts

For a request case `r` and a boundary `b`, the type system needs facts with
these meanings under assumptions `GAMMA` and condition `phi`:

- `accepts(r, b)`: this boundary accepts this request under the condition.
- `passes(r, b)`: this boundary does not accept this request under the
  condition, so selection continues outward across it.
- `selects(r, K, result)`: within context `K`, the request selects the stated
  boundary with its crossed prefix and outside context, or goes outward after
  crossing the stated prefix, for every feasible execution satisfying the
  assumptions in which that request occurs. For a suffix `K`, the judgment
  concerns the search position reached after the preceding boundaries pass,
  with the same request, activation and surrounding control facts.

These are candidate judgments, not chosen Ash syntax or a decision that the
language already expresses every condition. A `phi` is an explicit condition
under which the conclusion holds, not an assumption that the condition is
true for every use. When neither acceptance nor passing is established
unconditionally, the account needs conditional cases or another conservative
representation that covers both possibilities. It cannot turn failure to
prove acceptance into proof of passing.

The rules below use exact **conditional** conclusions: under a case condition,
every applicable execution has the stated selection. A conservative
may-selection set is different: it must contain every concrete outcome, but
membership does not assert that the member occurs under every valuation. A
may-selection must not be used as a proved exact selection. The design must
state the coverage and downstream safety rule for whichever account it uses.

For an ordinary source handler, acceptance requires the same effect identity
and all instantiated arguments to be equal. Definite identity or argument
inequality establishes passing. At runtime a [builtin cell selection](../../../spec/dynamic-semantics.md#scoped-cell-execution) matches
the request's lexically instantiated activation against the live boundary;
generic cells also match the complete instance. The selected provider then
authenticates the operand handle against that activation. The static analysis
uses possible abstract operand targets to reason about those relationships;
it does not observe a runtime target. Native and excluded interpreter boundaries supply
their own acceptance and passing facts through their contracts. A
non-interpreting frame passes for selection while retaining its owner and
completion facts. An opaque context with an unknown possible boundary cannot
be treated as transparent without an established passing fact.

A row-tail lacks fact can exclude a request from that **tail** when its
conditions hold; it does not erase a separately known row member or prove the
callee's payload, residual control or dependencies. No rule may invent a
lacks fact merely to make a desired selection work. Boundary-specific premises
can also precede selection: for example, an excluded retained-control
operation supplies its own preselection obligation even when a source handler
would intercept. This record does not replace that outside-slice rule.

## Candidate composition rules

The rules below use an ordered context written `b :: K`, with the innermost
boundary or frame first. `selected(b, prefix, outside)` records a selected
boundary, the control crossed before it and the context beyond it.
`outward(prefix)` records passage beyond the described context. These are
judgment results, not runtime data structures or proposed Core syntax. The
conditions and contracts must identify actual relevant subjects and
activations; a static source site alone is not a runtime owner. The premise
`case(r, K)` identifies an established possible request/context pairing under
the condition; it does not assert that the request executes.

If the innermost candidate accepts, selection stops there; `K` is outside it:

```sequent
S-Here :=
  GAMMA, phi |- case(r, b :: K)
  GAMMA, phi |- accepts(r, b)
  ===>
  GAMMA, phi |- selects(r, b :: K, selected(b, [], K))
```

If it passes and an established selection judgment for the remaining context
selects `h`, the new composition adds `b` to the crossed prefix. The rule uses
the established conditional judgment for `K`; it does not reopen `K` to
rediscover that fact:

```sequent
S-Through :=
  GAMMA, phi |- case(r, b :: K)
  GAMMA, phi |- passes(r, b)
  GAMMA, phi |- selects(r, K, selected(h, prefix, outside))
  ===>
  GAMMA, phi |- selects(r, b :: K, selected(h, b :: prefix, outside))
```

If the certified described context is empty up to its composition boundary,
the request remains outward to whatever context is composed next. An unknown
or omitted suffix is not evidence of an empty context. Passing one more
boundary preserves the outward result and records that crossed boundary:

```sequent
S-Outside :=
  GAMMA, phi |- case(r, [])
  ===>
  GAMMA, phi |- selects(r, [], outward([]))

S-Through-Outside :=
  GAMMA, phi |- case(r, b :: K)
  GAMMA, phi |- passes(r, b)
  GAMMA, phi |- selects(r, K, outward(prefix))
  ===>
  GAMMA, phi |- selects(r, b :: K, outward(b :: prefix))
```

These rules describe one case at a time. For composition, request, boundary
and suffix judgments may have different conditions and lexical substitutions.
Instantiate each under its own stated assumptions and compose them under the
conjunction of the applicable conditions, using justified weakening or
entailment. A complete composition must establish that its cases cover every
feasible request and selection under its actual premises, and must satisfy each
downstream obligation under the condition for its case. It does not have to
prove either branch condition unconditionally. An unproved case cannot be
silently dropped. An outward case preserves the request, crossed-control facts
and pending assumptions in the resulting contract; a closed program must
satisfy its applicable interpretation premises.

The [matching and coverage record](first-slice-matching-coverage.md) develops
candidate source-handler match bounds and rules for combining conservative
may-selection outcomes. It does not treat a member of a may-set as an exact
selection.

This is a compositional rule schema, not a mandate to scan a verified
constituent's internal frames. A constituent can expose a selection judgment
parameterized by the relevant request and assumptions. A new composition uses
that established judgment and checks its own boundary relationship. How Ash
represents and instantiates such conditional judgments, establishes coverage,
and avoids repeating an already established fact is still a design problem.
The rules do not authorize reconstructing a constituent's behavior from its
body or a graph of it.

## Polymorphic example

Suppose a certified request case is `E<T>.ask`, with an inner `E<U>` source
handler and an outer `E<T>` source handler. Both handlers have their ordinary
typing and coverage premises established, and any intervening boundary is
known to pass the request. At this selection point:

| Condition | Selection and crossed control |
| --- | --- |
| `T = U` | The inner handler is nearest; selection does not reach the outer handler. |
| `T != U` | The inner handler is crossed and the outer handler is nearest. The inner boundary is part of the crossed control. |

If the type system does not establish equality or inequality, it must account
for both feasible cases and keep their conditions correlated with their
capture and completion obligations. These conditions are metanotation for the
design; this record does not claim current Ash has a general type-level
inequality proposition or a solver for it. The existing
[imported-handler test](../../../tests/effect_modules.rs#L133) executes
distinct and coincident specializations of a related program whose inner body
also explicitly requests `E<U>`. This table concerns the later `E<T>` request;
it does not bypass the ordinary requirement that a handler's target appear in
its body's row. The test was inspected, not run for this record.

## Instantiate guarded cases and row facts

The same generic substitution and evidence rules apply to requests, handlers
and their rows. A later instantiation can make previously distinct symbolic
arguments equal, so it must preserve guarded alternatives rather than assume
that an earlier possible mismatch remains a mismatch. It must also preserve
the subject and scope of each inherited fact; it does not recheck the
certified request, handler or clause.

Let `Cases = {(g_i, J_i, O_i)}` be a certified covering family for one
subject under assumptions `GAMMA; Phi`, with outer and coverage obligations
`O_outer`. Each `J_i` concerns that case's request,
ordered context, lexical instantiations and local witnesses; `O_i` contains
its still-open obligations. `sigma` substitutes type and row parameters,
not dynamic activation witnesses. Every closing valuation of the new context
must give an admissible valuation of the original contract under `sigma`.
Well-kindedness, scope, row lacks and other original constraints are required;
failure to prove a constraint is not a proof of its negation.

```sequent
J-Guarded-Contract-Specialize :=
  GAMMA; Phi |- certified(subject, Cases) [O_outer] and Cases covers the applicable behavior under those obligations
  sigma is capture-avoiding, well kinded and preserves each contract binder and witness scope
  GAMMA_new establishes GAMMA[sigma], or retains each missing same-scoped premise as O_fit
  Phi_new entails Phi[sigma] and the instantiated constraints for every admitted closing valuation, or retains those same-scoped obligations O_constraints
  the same actual subject and its saved lexical instantiations are related by the certified specialization
  Cases_new carries each g_i[sigma], J_i[sigma] and O_i[sigma] with its original local binders, unless that guard is proved infeasible under Phi_new
  O_spec carries O_outer[sigma], O_fit, O_constraints, all applicable case and coverage obligations and new specialization proof obligations under their original guards and binders
  ===>
  GAMMA_new; Phi_new |- certified_specialization(subject, sigma, Cases_new) with complete conditional coverage [O_spec]
```

This is an application of the existing [certified-use and instantiation
interface](first-slice-judgment-requirements.md#use-an-established-judgment),
not a new pass over the certified body. A newly composed boundary still checks
its own relationship with the specialized contract. `T = U` and `T != U`
remain distinct guards until established or refuted under the new assumptions.
If `sigma(T) = sigma(U)`, the unequal branch is removed only by a justified
contradiction; if equality is unresolved, neither branch can be silently
discarded. Type-argument coincidence does not identify distinct dynamic
handler or continuation activations. Each retained obligation stays attached
to its own case and witness scope.

An inherited least row needs a separate distinction. A single row covering
all original cases remains a valid **upper bound** for the restricted cases
only when the applicable substitution and row relations establish that
preservation. It need not remain *least* after specialization removes cases
or coalesces equal members. For example, a formerly possible contribution
from a now-infeasible case can make the inherited row larger than necessary.
Ordinary partial union, exact removal and row-tail lacks must each succeed
under their stated conditions; a substitution does not automatically commute
with an unresolved partial operation.

For this argument, `denote(row,valuation)` and `leq` are the established
meaning and inclusion relation of the applicable rows, not a new row syntax
or an assumption that a partial operation succeeds. `map_sigma(tau)` maps an
admitted closing valuation `tau` of the new context to its original-context
valuation. The case correspondence below covers each actual specialized case
and relates its requirements to that same original case. Obligations on the
source upper bound, substitution, case correspondence and row relation stay
attached; they cannot be used as unconditional evidence.

```sequent
family row-specialization-evidence:
  J-Specialize-Row-Upper :=
    GAMMA; Phi |- rho is an upper bound for every applicable case in Cases [O_source]
    GAMMA_new; Phi_new |- the instantiated original GAMMA[sigma] and Phi[sigma] assumptions hold, or retain their same-scoped obligations O_context
    GAMMA_new; Phi_new |- every admitted closing valuation tau maps under sigma to an admissible original valuation map_sigma(tau), including all kind and original instantiation constraints [O_sub]
    GAMMA_new; Phi_new |- for every feasible specialized case c_new at tau, a corresponding applicable source case c_old at map_sigma(tau) has leq(requirements(c_new,tau),requirements(c_old,map_sigma(tau))) [O_cases]
    GAMMA_new; Phi_new |- rho_new is well formed and for every admitted tau, denote(rho_new,tau) = denote(rho,map_sigma(tau)) [O_row]
    the applicable row relation is transitive for these related denotations
    O_upper carries O_source[sigma], O_context, O_sub, O_cases, O_row and any new proof obligations under their original guards and scopes
    ===>
    GAMMA_new; Phi_new |- rho_new is an upper bound for the specialized cases [O_upper]

  J-Specialize-Row-Least :=
    GAMMA_new; Phi_new |- rho_new is an upper bound for the specialized cases [O_upper]
    GAMMA_new; Phi_new |- certified leastness evidence proves rho_new is no greater than every admitted upper bound for these same specialized cases [O_least]
    O_result carries O_upper and O_least with their original guards and scopes
    ===>
    GAMMA_new; Phi_new |- rho_new is least for the specialized cases [O_result]
```

The first rule requires the actual substituted row relationship; it does not
guess `rho_new` from type spelling. The second consumes a proof of leastness
for the **restricted** case family, rather than deriving it from an inherited
upper bound. Existing [guarded least-row evidence](first-slice-close-derivation-rules.md#reuse-a-guarded-least-row-fact)
can supply such a proof when its guards and universal premises match; it was
developed for close rows and does not by itself establish a generic handler
row theorem. The [row rules](../../../spec/static-semantics.md#computation-types-and-effect-rows)
and [handler rule](../../../spec/static-semantics.md#effects) remain current
authority. How to represent and produce the general guarded contract,
substitution-preservation and specialized leastness evidence—including open
tails and coincident instances—is an open design and correspondence gap.
An unresolved row or coverage obligation cannot be treated as an absent
effect or as a least-row proof.

## Connection to capture and correctness

For a selected source handler, the
[capture rule](first-slice-request-capture-judgments.md#select-a-source-handler)
uses the selected boundary and crossed prefix to establish the clause-local
capability and its owned segment. It separately checks payload crossings. A
cell or native selection uses its own contract. For an outward result, the
request and crossed-control obligations remain available to the enclosing
composition. Resume, discard and their effects remain separate rules.

The proposed selection rules must be justified against the specified runtime
search, including lexical instantiation, possible generic coincidence and
actual cell targets. They must also establish coverage under recursion,
unknown calls and opaque boundaries. Those justifications, a concrete
type-level representation and a working checker remain open. The rules are one
necessary part of ruling out an unmatched or incorrectly interpreted request;
they do not by themselves prove the narrow correctness of a whole program.
No existing verifier is shown removable by this record.
