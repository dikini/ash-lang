# First Slice: Request and Capture Judgments

This record develops the request/capture composition in E10 of the
[catalogue](first-slice-catalogue-and-map.md#effect-handler-and-control-rules).
It builds on the [implementation trace](first-slice-capture-composition-trace.md),
[continuation-use trace](first-slice-continuation-use-trace.md) and
[discard trace](first-slice-discard-ownership-trace.md). Its candidate
judgments and rules are design work, not current Ash semantics, a complete
calculus or an implementation decision. The [specification](../../../spec/README.md)
states current behavior.

The question is what an already checked computation must expose so a new
surrounding context can establish the request, capture and completion facts
needed by its own rules. The computation and its context are opaque at that
composition boundary: their established judgments are inputs, and neither
constituent is checked again. Ordinary function definition and application are
outside this slice; an invocation's established computation judgment enters
here as a boundary fact.

## Current checks and intended disposition

The table identifies the subject and result of the current path. The last column
is a proposed disposition for this slice, not permission to remove a check.
Current [Core validation](../../../spec/elaboration.md#validation-boundary)
remains required until the applicable specification and decision change.

| Current producer or check | Input and established result or failure | Intended typed disposition |
| --- | --- | --- |
| [Request elaboration](../../../src/elaborate.rs#L13966) and [Core request checking](../../../src/core/validate.rs#L15806) | The exact operation contract and operand give a typed request, result and row; incorrect identity, types or row reject. | Establish and retain the request's ordinary type and row once, plus the additional behavioral facts needed below. A handler composition consumes these judgments without retyping the request. |
| [Module capture publication](../../../src/elaborate.rs#L5791) | Local roots, imported global and method summaries and selected method routes produce checked callable summaries or a failure. The current [summary](../../../src/core/capture.rs#L75) contains a selected abstract value and an optional immutable graph; a missing summary is unknown. | The checked constituent must expose its type-system contract, including its assumptions and relevant request/control facts. Reuse that contract at every applicable composition. The present graph is not yet that certificate. |
| [Close-row inference](../../../src/core/capture.rs#L3243) | When pending close rows require it, the graph query returns contextual cleanup requirements; the [row solver](../../../src/elaborate/cleanup_rows.rs#L392) uses local requirements and retained interpreters in its equations. | Preserve this distinct row-inference output for its cleanup consumer until the cleanup typing rules establish and supply the corresponding row facts. It is not, by itself, a discard-safety proof. |
| [Strict capture checking](../../../src/core/capture.rs#L3282) | Checks control roots; where needed it collects row observations and checks their agreement. It also publishes initializer-reply information into the value graph before producing callable summaries. | Supply the distinct control, row-agreement and actual-reply facts to their applicable consumers. Their individual correspondence and disposition remain open; shared graph construction does not make them one judgment. |
| [Import and graph construction](../../../src/core/capture.rs#L364) | Imported summaries are keyed by binder; their graph and value information is relocated into a consuming analysis graph. The later analysis follows that representation in the caller's context. | Reuse already established judgments rather than rediscovering the constituent's behavior by traversing a representation of its implementation. Apply rules to the caller's new context and the stated contract. Precisely which current operations can be removed is not yet established. |
| [Other summary consumers](../../../src/resolved.rs#L11602) | Metadata closure authentication walks summary references; [dialect selection](../../../src/elaborate.rs#L24689) inspects retained-control information, and [region preparation](../../../src/elaborate/region.rs#L212) uses shared analysis. | Preserve these consumers and their required facts until their own dispositions are established. This request/capture rule alone does not replace them. |
| [Specialization and boundary matching](../../../src/core/capture/control.rs#L2712) | Request and boundary labels are instantiated in their own contexts. [Matching](../../../src/core/capture/control.rs#L2813) distinguishes definite equality, definite difference and possible equality; open-row lacks can rule out a candidate. | Preserve exact identities, substitutions and equality/lacks premises in constituent contracts. Derive possible nearest selections for the new context, retaining all relevant cases when equality is undecided. |
| [Selection and capture](../../../src/core/capture/control.rs#L5966) | The analysis finds possible nearest boundaries or outward escape; for a source clause it [checks crossed payloads and builds the selected capture](../../../src/core/capture/control.rs#L6156). | From certified request and context facts, establish the selected handler, its ordered captured segment, clause-local owner and outside obligations. The actual runtime selects one nearest boundary; static uncertainty may require several conditional cases. |
| [Resume and discard](../../../src/core/capture/control.rs#L7181) | A matching live owner can be consumed; resume restores its capture. Strict discard separately checks unknown selections, owned close and completion. | Apply the certified capability and capture facts. Resume and discard have distinct premises; in particular, prove closability only for discard, including the other slice rules' interpreter and row requirements. |
| [Assembled Core](../../../src/core/validate.rs#L13803) | After ordinary validation, the conditional capture gate reconstructs relationships from assembled nodes with empty imported-summary inputs and uses success or failure. | A checked Core constituent carries complete types and certified judgments. Check a new Core composition from those judgments and its new premises, without verifying the constituents again. The exact correspondence and disposition of each existing Core check remain open. |

The graph is shared with value, cleanup and excluded-slice consumers. Row
inference and strict safety also use it for different queries. A replacement of
the request/capture obligation does not, by itself, retire the graph or those
other checks.

## Candidate boundary contracts

Use the following metanotation to identify the facts. It is not proposed Ash
syntax and does not fix a tuple layout, effect-row extension, solver, proof
registry or concrete certificate format.

`GAMMA |- e : A ! epsilon ; B_e` means that the computation `e` has its
ordinary result and effect contract and a behavioral judgment `B_e`, under the
stated assumptions. The behavioral judgment must safely cover its possible
relevant requests and their relationships to continuation and completion. It
must at least provide, when needed:

- the exact effect and operation identity, arguments, lexical substitution and
  any conditions under which a request is possible;
- relevant facts about its particular operand and dependencies, and the
  assumptions needed for a particular interpreter reply to feed the residual
  computation;
- a contract for the computation's residual behavior at that request,
  including relevant later requests and completion obligations; and
- the assumptions, unknowns and equality or row constraints on which those
  facts depend.

These describe an upper bound on possible behavior, not a claim that every
listed request executes. Absence is usable only when established by the
contract; an ordinary effect row or a missing summary does not establish the
needed continuation or dependency facts. A contract must handle branching,
recursion and opaque callees soundly, but this record does not claim that a
particular finite representation or inference procedure has been found.

`GAMMA |- K : C_in -> C_out ; B_K` means that an enclosing context `K` accepts
the indicated computation contract and supplies a behavioral context judgment.
The relevant facts include ordered candidate boundaries and their own lexical
instantiations; owners and their phases; and where required completion is
scheduled relative to those boundaries. It must distinguish local and outside
owners and preserve facts of opaque constituents used to form the context.
Here `K[e]` is metanotation for composition, not a new source construct.

Both judgments may be conditional. Applying a judgment establishes its stated
conclusion only after its premises have been established, or leaves an
explicit conditional obligation. Core must carry complete types and the facts
needed to use established judgments. Surface inference may obtain them; neither
interface obliges a source programmer to write every fact.

### General residual interface: remaining producer gap

The protocol-parametric [authority transition and sequencing
rules](first-slice-judgment-requirements.md#apply-an-authority-protocol)
can move or consume authority and compose an established residual. They do
not by themselves produce that residual from an ordinary type, row or whole
result. The [general port-frame cases](first-slice-behavior-coverage-rules.md#constructor-specific-delimited-ports)
describe how a **new** context composes existing cases; an opaque constituent
must still provide the relevant delimited interface. In particular, two whole
residuals can agree while their captured segments and following clause work
differ, as the [counterexample](first-slice-behavior-coverage-rules.md#remaining-information-required-by-these-rules)
shows. Treating the whole residual as the captured segment would cross the
wrong boundary.

The missing general producer and consumer relationship is this:

- The first check of a computation must establish, or retain as an obligation,
  each applicable request possibility and its residual interface, or a proof
  that no such request is possible. The interface can be delimiter-parametric
  or expose an open local port: it need not predict a later caller's boundary.
  It relates the same request, actual operand, saved lexical instantiation,
  reply, local control and state, and covers its guarded requests, returns,
  failures, non-return and unknowns.
- A new enclosing composition establishes its own ordered boundary and exact
  conditional selection, then instantiates or extends the existing interface
  through its own context to the selected delimiter and composes it with the
  selected protocol and outside continuation. It retains each case's
  dependencies, authority and scoped obligations. A possible selection or row
  member is not an exact selection or proof that the request occurs.
- Resume, discard or a future continuation operation may eliminate that
  interface only under the **selected protocol's** actual authority and
  entry conditions. A normal reply enters the corresponding residual; a
  no-reply, failure, non-return or unknown case follows its own contract.
  Copying, repeated resumption or discarding is not inferred from the
  reusable description of the residual.

The current [selection analysis](../../../src/core/capture/control.rs#L6156)
and [clause construction](../../../src/core/capture/control.rs#L6760) trace
request and control relationships in the existing graph. They do not show
that a checked boundary already publishes this general type-level interface.
Its representation, initial producer, specialization and coverage—including
recursive or unbounded reply behavior—remain **design gaps**. An absent
interface stays an obligation; a consumer cannot silently reconstruct it by
reopening a certified fragment. The current structural one-shot checks and
applicable legacy consumers remain until their exact correspondence is
established.

### Extend an open residual through a new context

For an ordinary request whose operand has actually returned and whose
same-case request preparation and formation succeed, the general
[`Frame-Perform`](first-slice-behavior-coverage-rules.md#frame-transitions)
describes that request with its actual operand and an empty local reply
residual. Its enclosing context has not yet been selected. This is one guarded
case, not a claim that operand return alone establishes a request or that
preparation cannot fail. Preparation failures and unknowns remain in the
complete cover. The referenced `Port-Empty` applies to its specified source
selection and restore with the selected owner consumed; it does not by itself
establish a protocol-parametric immediate-reply identity for every kind of
interpreter. A general empty-port producer, including each applicable reply
protocol, and its typed-Core representation still need their correspondence
and failure evidence. An open request boundary is a logical decomposition of
the certified behavior, not a claim that the current evaluator suspends in a
physical request state there: its actual
[request routine](../../../src/eval/machine.rs#L4440) continues into frame
search. Correspondence must cover that search and its phased failures.

For a wider certified fragment, write `Open(r,K,R)` for an **established**
case in which request `r` reaches the fragment's own open boundary, `K`
describes the same pending local control, and `R(eta)` gives the correlated
continuation up to that boundary for an admissible actual selection and reply
case `eta`. This is metanotation for a scoped interface, not a fixed frame
list, a runtime continuation value or permission to resume. In particular,
the original producer need not know a future enclosing delimiter. `eta`
includes the same request `r`, selected boundary, reply, restored state,
dependencies and authority facts needed by the protocol. No-reply and failed preparation cases keep
their own contracts and do not call `R`.

The following is a general **pass-case** producer for a newly composed
context frame `f`. `append(K,f)` composes the already established local
control interface with that one new frame; it does not inspect the interior of
`K`. `ThenOpen` is the symbolic case composition supplied by the existing
port-frame and sequencing interfaces. It enters `f` only on a normal result
of `R`, carries earlier requests and their residuals with `f` pending, and
preserves the other covered outcomes. A later request may select `f` under
its own guard even though the original `r` passed it.

```sequent
J-Extend-Open-Residual-Pass :=
  GAMMA; L, phi |- the certified fragment has case Open(r,K,R) [O_fragment]
  GAMMA; L, phi |- f is the one new certified context frame with its conditional transition and authority contract [O_frame]
  GAMMA; L, phi, chi |- the local boundary f passes this same r, preserving its applicable control and outside obligations [O_pass]
  for every admissible actual reply case eta for r selected at or beyond the new open boundary, R(eta) has its certified cover and its normal entries fit f's transition, or retain the same-scoped O_fit(eta)
  under each such eta, the generic port-frame and sequencing cases cover all applicable request, selected-interpreter, return, failure, non-return and unknown outcomes of composing R(eta) with f, or retain covering O_cases(eta)
  R_new(eta) = ThenOpen(R(eta), f) for that same eta and its guarded state, value, dependency and authority facts
  O_open carries O_fragment, O_frame, O_pass, each O_fit(eta) and O_cases(eta) universally scoped under that eta's admissibility guard, and new proof obligations with their original subjects, guards and binders
  ===>
  GAMMA; L, phi and chi |- the new composition has case Open(r,append(K,f),R_new) [O_open]
```

The conclusion is relative to the **new composition's** open boundary; no
future enclosing delimiter is guessed: the pass premise decides only how `f`
treats `r`. Its `eta` binder is shared by the reply,
restored local behavior and subsequent frame transition, and the selected
authority protocol governs whether that case is admissible. The rule neither
executes the reply nor duplicates authority. Cases where `f` accepts the
original request use the corresponding certified selection and interpreter
composition instead; an undecided match retains both feasible guarded cases or
a covering unknown. An outward case does not establish that an enclosing
interpreter or reply exists. No-reply, abandonment, failures and non-return
remain in their own covered cases rather than being turned into calls to
`R_new`.

This rule reuses the fragment and frame certificates, including the
reply-parametric residual certificate, and checks only their new case fit; it
does not check that residual afresh for each reply. It does not provide `Open`
for an arbitrary opaque fragment: its
first checker or an established boundary contract must supply that interface,
or leave it as an obligation. Proving the proposed `ThenOpen` composition and
its complete case/obligation transport, including a recursive or unbounded
residual, remains a general design and correspondence gap. No current
verification can be retired merely from this schema.

### Effect-parameter requirements at request boundaries

Current Ash's [effect-instance formation](../../../spec/static-semantics.md#computation-types-and-effect-rows)
checks the declared parameter kinds and arity. Its
[effect declarations and requests](../../../spec/static-semantics.md#effects)
do not declare an interface requirement on an effect parameter, and an effect
row does not itself select interface evidence. For example, a requirement
`I<T>` attached to a future effect declaration `E<T>` is a proposed general
facility, not an existing requirement of every `E<T>` or a special rule for
one effect. The requirement's declaration, evidence scope and Core form remain
to be specified.

For a declared requirement `I<alpha>`, let `sigma` be an admitted
instantiation of the *same* effect parameters. The common evidence and
composition rules must support the following relationships:

1. **Formation and a generic boundary.** Instantiation produces the requirement
   `I<sigma(alpha)>` under the corresponding remaining binders and assumptions.
   The applicable evidence can be an established implementation selection or
   an abstract assumption at a generic boundary; otherwise retain the scoped
   obligation.
   A declared requirement is not evidence of its own satisfaction. Which row
   and declaration occurrences must establish or retain it is part of the
   missing formation design.
2. **Request.** The new `perform` composition uses the operand's existing
   judgment and the authenticated operation's instantiated contract. It
   carries the same applicable requirement and evidence or obligation alongside
   the exact instance, parameter substitution and any evidence dependencies.
   The operand's failure, request and non-return cases remain separate; an
   established operand is not checked again. A row member or operation spelling
   alone does not prove the requirement or select a handler.
3. **Handler and selection.** A handler for that exact instance retains the
   requirement and whichever scoped evidence its own checked clauses use.
   Nearest selection still depends on effect identity, arguments and ordered
   control. When a selected request and handler compose, the common rules must
   establish any required relationship between their evidence under the same
   actual instantiation and scope, or retain it as an obligation; equal effect
   instances alone do not prove two evidence values identical. The bound does
   not itself change runtime selection, grant authority or prove a clause's
   behavior.
4. **Source to Core and later uses.** Elaboration preserves the instantiated
   requirement, evidence or scoped obligation and its dependencies with the
   same source/Core binder and subject correspondence. It reuses each checked
   child's and implementation's certificate and checks only the new request or
   handler composition. Core must carry enough explicit type and evidence
   information for its certified boundary, including the scope of any
   abstract assumption. The representation may be a checked reference or other
   admitted form; this requirement does not prescribe a field on each node or
   a runtime dictionary where no computation needs one.

Once those premises and evidence exist, the candidate
[`J-Use-Certified`](first-slice-judgment-requirements.md#use-an-established-judgment),
[`J-Apply-Operation-Contract` and `J-Apply-Handler-Contract`](first-slice-judgment-requirements.md#introduce-and-apply-declared-contracts),
and [`J-Lower-Certified-Composition`](first-slice-judgment-requirements.md#carry-a-checked-source-judgment-into-core)
provide the shared reuse, composition and lowering relationships. They do not
by themselves establish the missing effect-formation or evidence-transport
premises.

The current Core [`RequestNode`](../../../src/core/effect.rs#L101) stores an
effect instance, operation identity and operand, and [`HandlerNode`](../../../src/core/effect.rs#L246)
stores its target and clauses. Current [request validation](../../../src/core/validate.rs#L15806)
authenticates the instance and operation and checks the operand, result and
row, but does not validate this proposed parameter requirement. Existing
interface evidence elsewhere in Core is not evidence that those node
relationships are already carried. The concrete source and Core representation,
formation and substitution rules, evidence availability at each boundary,
dependency crossing and source/Core correspondence remain design gaps. A
missing piece stays a scoped obligation; it is not discharged by reselecting
or rechecking a previously certified implementation.

## Candidate composition rules

The rules below describe what must be derived. Their named relations still
need definitions and a checking procedure; writing them as premises does not
prove they can be established.

### Form a new context

Given certified `e` and `K`, the new composition `K[e]` must establish that
their types, parameters and assumptions fit. Its behavior is derived from
`B_e` and `B_K`, including all relevant request and continuation relationships.
This is a new composition judgment: it may check new equality, row, crossing
and ownership premises. It must not check `e` or `K` again or traverse a
stored representation to reconstruct facts already established for either.
The implementation of this rule, including how it avoids that repetition,
remains to be designed.

For a request case from `B_e`, the context rule considers the request's saved
instantiation and each candidate boundary's own instantiation. Exact identity
and all arguments determine the effect-instance match for an ordinary source
handler. A builtin cell matches the request's lexically instantiated activation
to a live boundary; its selected provider separately authenticates the actual
operand handle. Other boundary kinds supply their own selection premises. If
facts do not settle whether a
polymorphic candidate matches, preserve both the matching possibility and the
possibility that selection continues outward, with their conditions. A
definite mismatch crosses the boundary. An unresolved open tail does not
prove absence. An outward request is retained in the resulting contract if it
is not handled here; a closed program must ultimately satisfy the applicable
interpretation premises.

### Select a source handler

For one possible selection, let `segment` denote the request continuation
through the nearest accepting source handler and `outside` the context beyond
it. A candidate selection judgment must establish all of the following from
the already checked request, context and handler contracts:

1. The selected handler matches the instantiated request and no nearer
   boundary accepts it under this case's assumptions. Account separately for
   cell and native candidates, including their own selection premises.
2. The operation payload may cross each relevant owner in `segment`; any
   dependency fact needed for this conclusion is established or remains an
   obligation. For an opaque call whose request payload is not directly known,
   account for the relevant callable and argument dependencies as well. The
   exact mapping of those current checks into boundary facts remains open.
3. The selected clause receives its local capability `k` as available and
   owns `segment`, including relevant nested live captures and completion
   facts. The handler and segment move out of the active clause context;
   their facts remain associated with the capture.
4. `outside` and its obligations remain outside. A request from the selected
   clause is composed with any control introduced locally in that clause,
   then its clause-owner boundary in its current state, then `outside`. A
   request to an outer handler can cross a live boundary and capture its owned
   segment; a consumed boundary contributes no further capture. The moved
   handler and segment are not active around the clause. A locally installed
   handler can therefore be the nearest match.

The handler's ordinary coverage, pattern, answer and row premises also apply.
The clause judgment can be certified under assumptions about its capability
and capture; the selection composition must establish or retain those
assumptions for each relevant possible selection. The operation introduces an
owner/capture fact, moves control facts between contexts, and preserves outside
facts. It does not discharge the owned completion obligations merely by
capturing them.

The following schematic rule names the inputs and conclusion for one possible
source-handler selection. `request_case` is an established behavioral fact
about a possible request and its residual computation, not a claim that the
request executes. `context_case` supplies the relevant ordered context by
composing the request case's certified local-control facts with the enclosing
context's certified facts. Thus `inner` includes applicable local boundaries
inside `e` as well as those contributed by `K`; neither constituent is
inspected. `nearest_source` includes the exact-match and no-nearer-match premises.
`fits` checks that the instantiated computation contract meets the context's
input contract, including its assumptions. `crossing_ok` stands for the
separate resource crossing judgment. The result
is conditional on `GAMMA` and binds a fresh local owner `k` for this selection.
It does not itself discharge any clause or discard obligations.

```sequent
J-Source-Capture :=
  GAMMA |- e : A ! epsilon ; B_e
  GAMMA |- K : C_in -> C_out ; B_K
  GAMMA |- fits(A ! epsilon ; B_e, C_in)
  GAMMA |- request_case(B_e, request, residual)
  GAMMA |- context_case(B_e, B_K, request, residual, inner, handler, outside)
  GAMMA |- nearest_source(request, inner, handler)
  GAMMA |- crossing_ok(request, inner)
  GAMMA |- clause_contract(handler, request, clause)
  k is fresh for this clause activation
  segment = selected_capture(inner, handler)
  ===>
  GAMMA |- capture_case(K[e], request, clause, k, segment, outside)
```

For a complete composition, the rules must derive a covering set of these
cases and any cell, native or outward cases, retaining their conditions. The
candidate rule uses the established cases; it does not say how `request_case`,
`context_case`, or their coverage is represented or derived. In particular,
`nearest_source` must be derived from identity, substitution and boundary facts,
not granted simply because this rule names it.
The [nearest-boundary judgment record](first-slice-nearest-boundary-judgments.md)
develops candidate acceptance, passing and conditional selection rules for
this premise.
The [request and sequencing record](first-slice-request-sequencing-judgments.md)
develops how request and pending-continuation facts can be introduced from
certified operands and binding constituents.

### Complete the selected capability

The [usage rules](first-slice-continuation-use-trace.md#candidate-usage-judgments)
and ordinary resume contract establish that the matching `k` is available
after its operand, then consume its availability. Resume restores its selected
segment in order above the remaining clause continuation. The actual resume
operand supplies the request's reply: its certified value and dependency facts
must be related to the request result and preserved for later consumers. The
rule also preserves the segment's resource and completion facts. It does not
replay the prefix before the request. A selected capture need not be
discardable merely to resume it. Other interpreters supply their actual reply
facts through their own boundary judgments; the ordinary result type alone is
not a proof of resource independence.

Discard also consumes availability, but additionally requires the
[owned-close premises](first-slice-discard-ownership-trace.md#candidate-judgments-and-discard-rule):
the recursively owned close plan, preservation of outside and running
completion, interpreter compatibility and least residual close row. Closing is
scheduled before the clause continuation; its obligations are not declared
completed at type-check time. Missing safety facts remain obligations and
cannot justify an unconditional discard. The current one-shot rules say
nothing here about future permission to duplicate a continuation.

## One certified computation, different contexts

The following comparison shows why a request's continuation belongs in the
facts that compositions use. The shared declaration and computation are shown
once. Treat `e = ask ()` as an opaque computation with one established
judgment under the same declarations in both contexts. Its contract says that
`B.ask` can be requested and supplies the relevant residual behavior. The
ordinary source arrow also carries the canonical default allocation requirement
`delta`; handling `B` does not discharge it. The examples are schematic
separate program fragments, not evidence that current Core implements
certification.

```ash
effect A {
    ask : Unit -> Unit
}

effect B {
    ask : Unit -> Unit
}

ask : Unit -> Unit ! {B}
ask () = perform B.ask ()
```

Write `rho_e` for the established behavior of `e` after its `B.ask` request
is resumed. This is an abstract fact from the checked computation, not an
instruction to inspect the body of `ask`. It does not say that the request
must happen or that every handler resumes it.

Now put a following computation `s` after `e`. If `e` requests `B.ask` and
the handler resumes it, the continuation is `rho_e`, followed by `s`. A
sequencing rule must derive that relationship from the established judgments
of `e` and `s`. The effect row records the possible request; the continuation
fact records what remains to be done if it is resumed.

The two contexts below use the same abstract judgment of `e`. Their written
`ask ()` occurrences are separate source compositions: each has its own
context premises, while the callable's established facts are reused. The
examples do not claim the current compiler already performs this reuse as a
complete Core certification.

In each case the `A` clause has an available owner `a`. First, place `e`
inside a local `B` handler, with `a`'s scheduled completion after that handler:

```ash
ask ignored => {
    let _ = handle (ask ()) with B {
        ask ignored => discard
    }
    resume ()
}
```

The selected `B` capture ends at that local `B` boundary. The live `A` owner
and its scheduled `resume` remain in the surviving clause continuation:

```text
B's capture:    rho_e, through the B boundary
Outside B:      resume the A capability
```

Given the other discard premises, the composition can establish that closing
the `B` capture does not skip `a`'s completion. The existing
[direct/helper case](../../../tests/effect_typing.rs#L235) checks this shape.

Now move the same scheduled `A` completion inside the body handled by `B`:

```ash
ask ignored => {
    let _ = handle ({
        let _ = ask ()
        resume ()
    }) with B {
        ask ignored => discard
    }
    ()
}
```

The request and `e`'s judgment are unchanged. The new context places the
scheduled `A` resume in the segment captured by `B`, while the `A` owner is
outside that owned capture:

```text
B's capture:    rho_e, then resume the A capability, through the B boundary
Outside B:      the still-live A capability
```

Discarding the `B` capture would skip that completion, so the composition must
reject or leave the required safety
premise unproved. The existing [negative case](../../../tests/effect_diagnostics.rs#L210)
has this structure with a direct request; it is evidence for the required
behavior, not a run of this helper variant. If the selected clause resumes
instead, apply the resume premises rather than imposing discard safety.

Thus the new fact is the relationship between a request and **this context**:
where the selected boundary lies, what it owns and where the outside
completion is scheduled. It is not a second proof of `e`'s request behavior.
Current tests do not instrument or establish reuse of a complete Core
certificate; this example states the intended rule and its acceptance cases.

## Sufficiency and remaining work

For each possible request and selection, the eventual rules must derive the
needed facts without opening certified constituents and must identify the
consumer of each result. They must cover direct and delegated requests,
polymorphic coincidence, later requests after resume, repeated activations,
unknown calls, and the ownership and interpreter premises of discard. Existing
[imported polymorphic cases](../../../tests/effect_modules.rs#L133) exercise
both coincident and distinct instantiations; the
[unknown-call cases](../../../tests/effect_diagnostics.rs#L233) reject an
unproved discard while permitting resource-free resume. These tests were
inspected, not run, and are not a proof of the proposed rules.

The central open design is a sufficiently expressive compositional behavior
and context contract, with rules for constructing and combining it and a
working checker. The before/after table does not show that any existing check
can yet be deleted, or that all of its consumers have been covered. Resolve
that mapping and the Core validation authority before replacement. Separately
established system-level proofs must justify that satisfying the final rules
rules out the in-scope execution errors under their stated premises; the other
slice rules and boundary facts are also required for narrow correctness of a
whole program.
