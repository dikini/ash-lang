# First Slice: Rule Resolution Status

This record joins the candidate rules to the
[catalogue](first-slice-catalogue-and-map.md#rule-catalogue). A candidate rule
is not resolved merely because it names the fact it needs: it must also say
how the fact is established and composed from certified inputs. No entry below
claims a completed checker, system-level proof, or permission to remove a
current verification path. The [specification](../../../spec/README.md)
remains authoritative for current Ash.

The follow-on records develop the remaining premises further:
[behavioral coverage](first-slice-behavior-coverage-rules.md),
[dependency covers](first-slice-dependency-cover-rules.md),
[owned-close derivations](first-slice-close-derivation-rules.md), and
[failure judgments](first-slice-failure-judgments.md). They define candidate
introductions and compositions while identifying the producers and proofs that
still have to be established. The
[Core judgment and certified-use rule](first-slice-judgment-requirements.md#candidate-core-judgment-form)
state how ordinary types, rows, behavioral facts and outstanding obligations
are carried and reused. The [source-to-Core composition rule](first-slice-judgment-requirements.md#carry-a-checked-source-judgment-into-core)
identifies the correspondence needed for the new Core subject without
rechecking its certified children; constructor correspondences and affected
consumers still require justification.

## Three categories

The slice distinguishes three roles. A fact or component can participate in
more than one role, but the roles must not be conflated:

1. **General type-system language and rules.** Types, kinds, interfaces,
   effects, resource and operation contracts, propositions, authority and
   composition judgments are expressed and checked through shared rules.
   Some forms and rules exist today; others are design gaps. This category
   does not assume a new user-extensible resource facility.
2. **Legacy.** This includes existing specialized analyses and validation
   paths whose facts the shared judgments are intended to express, as well as
   constructs or implementations explicitly identified as legacy. The
   separately proposed [legacy integer-cell removal](../../proposals/CP-0031-remove-legacy-integer-cell.md)
   is a semantic change; it is not current language behavior. Verification
   paths are the before-state for this migration and remain in place until
   their particular obligations and consumers are covered. A path still
   needed for an unverified subject or a shared consumer must remain until
   that need is addressed. An ordinary existing type-system operation is not
   legacy solely because a legacy path calls it.
3. **Instances and implementations.** Concrete declarations, builtins,
   handlers and runtime operations instantiate or implement contracts from
   category 1. Their behavior and failure phases supply correspondence
   evidence. Runtime implementations are not legacy merely because a
   current verification path checks facts about them; their semantics must
   continue to be accounted for by the declared contracts and common rules.
   Current Ash builtins include special cases introduced when the language
   lacked the necessary capabilities. Builtin status is not presumed to be
   permanent: each in-slice builtin is evidence for identifying those missing
   general capabilities and the contracts an instance must satisfy. This does
   not presume that its runtime implementation must be removed or rewritten.

The intended cell direction is a variable of type `T` with **mutability as a
type-system property**, alongside the applicable location and usage
properties. General state and type rules and any applicable effect rules
govern its operations; the property does not itself determine a particular
state-effect protocol or introduce a separate resource or owned object. **Current Ash
has no general form that expresses this property**; this is a design target,
not an existing ordinary binding or a completed choice of mutability model.
How it attaches to a binding, value or access, and its syntax or inference,
remain open. Allocation, disposal, lifetime and
completion belong to its applicable resource contract; the variable does not
introduce a second cell-specific owner or resource protocol. The current
generic builtin's separate scoped owner is a **legacy candidate** to compare,
not a claim that current Ash already has the intended representation or that
the two behaviors are equivalent. The comparison must identify any semantic
change and preserve all relevant dependency, access, interception, snapshot,
capture, release and failure obligations. Region and arena implementation
remain outside the slice; their established facts enter only through the
existing boundary.

The [specification](../../../spec/README.md) remains the authority for the
current language. These categories describe the intended type-system and
verification relationship; they do not declare that proposed forms already
exist or authorize implementation.

### Derive shared rules from actual instances

Concrete instances and implementations are where the difficult semantic
questions become visible. Use them as the starting evidence for each ledger
entry, including cases that cross data, effects, control and ownership. Follow
this method without creating an experimental implementation:

1. Trace the instance's intended operational behavior, declaration and
   implementation, including failure and opaque boundaries. For an in-slice
   builtin, identify separately any hard-coded declaration or authority,
   specialized verification, and runtime implementation. Record any
   specification/implementation discrepancy rather than treating code as
   language authority.
2. Identify the facts established, their producers and the consumers and
   existing verification paths that use them. Preserve subjects, scopes,
   guards and obligations; distinguish a repeated constituent fact from a new
   composition fact.
3. Determine whether existing general forms and rules express and compose the
   relationship, including facts currently supplied by builtin special cases.
   If not, record the missing capability and compare the general forms or
   rules that could supply it. Make and justify the design decision against
   the instance's required behavior, composition and reuse; state its
   consequences and any unresolved premises. Retain the instance's own
   declared contract. Unknown or unproved behavior remains an obligation.
4. Record the correspondence and eventual disposition of every affected
   legacy check and consumer. Keep an incomplete rule as a design gap; move
   to an implementation gap only at the stated readiness threshold. Reuse
   previously certified facts rather than creating a specialized checker for
   the instance.

This is a method for extracting and justifying the general type system from
real behavior, not a requirement that all instances obey one resource or
effect protocol. The existing traces remain the evidence for the ledger.

## Design and implementation gap ledger

The work now concentrates on **general** type-system judgments, declared
contracts and evidence reuse. The specialized checks below are current audit
evidence and migration obligations, not a request to add an equivalent
specialized rule or a second checking pass. The earlier candidate records
retain their derivations for this trace; their cell- or operation-specific
statements must ultimately be expressed through shared rules and declared
propositions where possible. **All entries are design gaps:** their
general rules, producers, consumers or required correspondence remain
insufficiently specified. An **implementation gap** is recorded only once
the applicable rule and its producer/consumer interfaces and correspondence
are specified well enough to implement; naming a candidate rule does not
meet that threshold. None of these entries authorizes implementation or
removal of an existing check. A verified constituent is reused, while a new
composition checks only its own relationships.

The first column identifies either a category 2 verifier or a category 3
implementation used as evidence. The second names the intended category 1
mechanism. The last identifies the missing category 1 contract or rule,
category 3 correspondence, or both; a proposed mechanism is not already a
verified instance.

For the initial effects-to-interfaces work, incomplete type checking of the
one-shot use of generated continuation functions is an accepted known issue.
Ordinary function types do not establish that property; suitable general usage
properties remain future work. This exception does not establish cleanup by
dropping a value, authorize escape, or change current Ash's structural checks.
See the [effects proposal](effect-interface-elaboration-proposal.md#current-behavior-and-intended-change).

| Current verifier (2) or implementation evidence (3) | Shared mechanism (1) | Exact remaining gap |
| --- | --- | --- |
| **(2) One-shot clause use:** [source and Core](first-slice-verification-audit.md#structural-usage-source-and-core-before-and-after) check clause identity, permitted scope and structural consumption. | Scoped authority and common sequential/alternative composition of a certified capability-use judgment. | Establish its producer and transport through actual clause and opaque-boundary scopes; the static `Consumed` marker alone is not proof of structural use or a dynamic owner. |
| **(2/3) Continuation as a function:** [ordinary functions are duplicable](../../../spec/static-semantics.md#effects), while a handler's continuation is currently nonduplicable and nonescaping. | Function types with general usage properties and scoped completion obligations. | Determine how a function contract expresses permitted application, duplication, escape and explicit discard. Current normally completing clauses consume the capability once by resume or checked discard; merely allowing an affine value to disappear does not establish cleanup. Future multishot and discard permissions must be considered independently. |
| **(2/3) Interface effect-row parameters:** the [specification](../../../spec/static-semantics.md#kinds-monotypes-and-schemes) excludes `EffectRow` in interface, implementation and method parameter lists. The checker nevertheless accepts and executes an interface with a row parameter and a closed-row implementation; [an existing test](../../../tests/effect_rows.rs#L405) also uses an interface row parameter. A method-local or implementation row binder instead reaches `kind.internal-state`. | Shared kind and row rules for parameterized interface contracts. | Reconcile the specification, admission and diagnostic paths before relying on interface row polymorphism. Determine which row parameters and constraints the contracts require and specify their checking and Core correspondence. Observed acceptance is not language authority; the internal diagnostic is not a normal source rejection. |
| **(2) Unknown call followed by discard:** the [traced path](first-slice-verification-audit.md#unknown-callable-request-reaching-a-discard) produces an opaque request alternative and rejects a selected unknown discard in the strict path. | A callable's general guarded request/residual contract, shared selection and capability/close composition, with unknown obligations carried at the boundary. | Establish complete callable and capture interfaces for the same selection and prove the close and outside conditions. An unknown case is not proof that a particular request occurs or discard is actually unsafe. |
| **(2) Unknown value at resource exit:** [`dependencies`](../../../src/core/capture/value.rs#L7294) projects away traversal completeness; [the concrete trace](first-slice-verification-audit.md#unknown-value-at-a-resource-result) shows an unknown-only body value is not selected by that candidate query. | A complete dependency-cover proposition for the actual value, with shared scope and boundary-crossing composition. | Prove the relation between graph atoms and complete actual-value covers, including scoped opaque inputs. An empty projected list does not prove independence; this one query does not prove whole-program admission. |
| **(2) Retained value and predecessor:** [`cell_retention`](../../../src/core/capture/value.rs#L5981) tests known root dependencies against enclosure or frozen predecessor sets. | Declared retention conditions applied through general scoped ownership, dependency and implication evidence, including applicable established region or arena facts, with previously established predecessor facts reused. | Determine which current cell requirements follow from a region-backed value's established facts and which need another general contract. Justify complete coverage and actual activation/enclosure across contexts. May-set overlap is not an actual-dependency proof. |
| **(2) Resource row removal:** [source](../../../src/elaborate.rs#L14309) and [Core](../../../src/core/validate.rs#L14133) check the cell scope's exact instance, with current `Missing` handling described in the [row account](first-slice-resource-rules.md#resolve-the-scopes-type-and-row-premises). The shared row operation itself can contribute to category 1. | General exact-instance equality, row relation and scoped contract application. | A [closed-row correspondence](first-slice-resource-rules.md#closed-row-missing-under-a-successful-resource-scope) derives absence using successful escape checks and scoped substitution in addition to `Missing`. An [open-tail trace](first-slice-resource-rules.md#open-tails-and-deferred-removal) identifies a conditional escape when the target's lack survives outward. Reconcile specification wording and establish remaining closed-tail, unresolved and deferred cases. An unresolved equality or tail is an obligation, not proven absence. |
| **(2/3) Generic-cell builtin declaration and verification:** [resource resolution](../../../src/resolve.rs#L11298) generates the exact provider and method forwarding declarations; [Core validation](../../../src/core/validate.rs#L14413) authenticates their current shapes and authority. | General declaration-bound operation and resource contracts, evidence production and scoped contract application. | Determine which missing general forms must express provider authority, forwarding behavior, identity and obligations, then establish correspondence to the existing declarations and all consumers. Do not assume the hard-coded admission or verification remains necessary. |
| **(2/3) Current generic-cell owner and implementation:** [runtime acquisition](../../../src/eval/machine.rs#L4210) and the [generic-cell execution semantics](../../../spec/dynamic-semantics.md#scoped-cell-execution) establish a distinct cell owner, read/write state and release behavior. That separate owner is a legacy candidate; the implementation is evidence, not automatically legacy. | A subject of type `T` with a general mutability property and applicable location/usage facts, using shared state and type rules and applicable effect rules; allocation, disposal and completion come from the resource, with no second cell-specific owner. | Compare the current and intended semantics and affected consumers, including access lifetime, interception, retention, snapshots, capture and failure. Specify missing general forms and any required semantic change; do not assume the region interface already supplies mutable state or that runtime code must be removed. |
| **(3) Selected clause and pattern:** [Core request dispatch](../../../src/eval/machine.rs#L4654) finds the selected clause and matches its actual operand; the [wildcard trace](first-slice-failure-judgments.md#exclude-a-selected-wildcard-clauses-nonmatch) excludes one particular nonmatch. | Shared authenticated declaration, selection, pattern and guarded case rules; reuse an established pattern interface for that actual subject. | Cover other patterns, lookup and match failures, allocation and disposal using general contracts. A proven wildcard case does not prove every pattern succeeds or that the clause body runs. |
| **(3) Discard preparation and owned close:** [runtime discard](../../../src/eval/machine.rs#L5254) inspects and reserves before transferring the selected capture; the [failure trace](first-slice-failure-judgments.md#source-handler-request-resume-and-discard-cases) records the phase states. | General guarded transitions, resource/authority movement, scoped completion obligations and failure propositions, composed with the selected capture's contract. | Produce a complete plan, owner and outside interface and applicable capacity, host and disposal evidence. An unproved capacity or close is not a proved failure, and successful transfer is not completed cleanup. |
| **(3) Cleanup start and finish:** the [runtime transition](../../../src/eval/machine.rs#L3372) starts the action and later checks its `Unit` result before returning the saved value. | A declared completion contract composed by the same generic sequencing, effect, state and evidence rules used for other behaviors. | Prove action-case coverage, phase and saved-value/dependency preservation through actual requests and finish, including failure observations. A possible action is not proof it runs or terminates. |

### Effect-to-interface elaboration and function properties

The following current Ash program handles a request and evaluates to `37`:

```ash
effect Trace<A> {
    record : A -> A
}

main : Unit -> Int ! {}
main () = handle ({
    let value = perform Trace<Int>.record 5
    value + 32
}) with Trace<Int> {
    record arg => resume arg
}
```

This separate current Ash program passes the corresponding function explicitly
to an interface method and also evaluates to `37`:

```ash
interface Trace<A> {
    record<R> : (A, A -> R ! {}) -> R ! {}
}

impl Trace<Int> {
    record (arg, k) = k(arg)
}

main : Unit -> Int ! {}
main () = {
    let continuation : Int -> Int ! {} = fn(value) {
        value + 32
    }
    record(5, continuation)
}
```

Both programs were run with the Ash interpreter. In the first, the remaining
computation inside the handling boundary is `value + 32`. In the second, it is
the explicitly supplied function. The request supplies `5`, `resume arg`
corresponds to `k(arg)`, and the resumed computation returns `37` to the
clause. The body containing the request has row `{Trace<Int>}`; the handler
discharges that instance and both the continuation and the whole handled
expression have the empty outward row.

For a requester-facing operation `P -> Q`, a handler operation needs a `P`
argument and a request-specific function `Q -> R ! epsilon`, and produces
`R ! epsilon`, where `R` and the outward row belong to the handling boundary.
The operation and handler method signatures differ; specifying their
relationship and the elaboration of `perform` and `handle` is an open gap.
The interface program manually supplies its function. It does not demonstrate
automatic capture, effect handling or all continuation and resource rules.

The continuation is a function value, not a separate type. The handler
interface and implementation receive it; they do not capture the request's
continuation. The function carries the captured computation and its
environment up to the handling boundary. The elaboration must preserve deep
handling when the function is called, including subsequent requests, and the
proposed installation-time context for handler clauses. How the required
context is supplied remains to be derived.

The example's `record<R>` must work for every `R`; its implementation can do
so because it returns the result of calling `k`. A handler that uses a
particular answer type, or transfers `k` and returns without calling it, is not
generally expressible by that implementation contract. Derive the contract for
the particular boundary result without treating universal `R` as a solution
for every handler. The closed empty row suffices above; [row parameter
support](#effect-row-parameter-audit) remains a separate gap.

The proposed type-system account uses general properties of function values
and their captures:

1. **Use and ownership.** A function contract records its permitted use and
   the obligations it owns. In the current nonescaping clause, each normally
   completing path consumes the capability by a call or checked discard. In
   the proposed escape extension, each owner must consume the one-shot value
   or transfer it and its obligations to a valid recipient. Transfer is not a
   call or discard. Affinity alone does not establish cleanup, and uniqueness
   alone does not restrict the number of calls.
2. **Lifetimes and dependencies.** Captured owned resources move only when
   their resource and storage contracts permit it. Dependencies not owned by
   the function must remain valid for both its possible call and its
   completion. Owning a resource does not extend the lifetime of its storage.
   Apply the same rules to any function, not a continuation-specific escape
   prohibition.
3. **Completion.** A checked discard consumes the same function ownership
   without calling it and completes owned captures under their contracts.
   Record the effects and dependencies of completion separately from those of
   a call. Preserve required outside and running completion; do not assume
   that dropping an affine value runs effectful cleanup. Type checking does
   not establish eventual termination or completion of a diverging program.
4. **Composition.** A function's established capture, use, lifetime and
   completion facts cross opaque boundaries as contracts. A move, call or
   discard checks its new relationships using those facts, without rechecking
   its certified body. Typed Core must retain the types, evidence and
   unresolved obligations needed for those checks; surface inference may
   supply them.

The current [static rules](../../../spec/static-semantics.md#effects) instead
expose a structural resume capability and forbid it from escaping its clause.
Permitting an ordinary function carrying captured control to escape is an
extension of current Ash semantics. Derive the transfer, lifetime and later
call or discard rules, including the destination of a later result, before
claiming that extension is implemented or safe. If the required facts are not
established, retain an obligation or reject the composition; do not treat
unknown ownership or completion as proof.

### Local implementations, handler boundaries and continuations

The [proposed installation-time handler context](../DN-0061-effects-and-resources-first-slice.md#proposed-handler-context)
uses local implementations of existing interfaces. It does not require local
type or interface declarations. Current [scoped evidence](../../../spec/static-semantics.md#scoped-exact-evidence)
already supplies methods that close over preceding values and evidence. The
following restrictions and their consumers must be revisited as general
interface rules, not through an effect-specific implementation mechanism:

1. **Local nominal in the key.** Today an exact local implementation must
   include an active local nominal in its selection key, so a local
   `Trace<Int>` is inadmissible. A future candidate is to allow any complete,
   well-kinded interface application, including one with enclosing rigid
   parameters. Continue to check its method set, types, evidence and scope.
   This does not introduce local generic implementation-head search or change
   module-level coherence and orphan rules by itself. Keep the current
   restriction while testing the present idea; the example above uses a
   global implementation.
2. **Simultaneously active keys.** Today identical active local keys are
   rejected. Nested implementations of the same exact effect contract need
   an applicable inner implementation while the outer one remains available
   outside it. Lexical shadowing of an identical complete application is a
   candidate. Specify whether sequential same-block bindings shadow, how a
   local binding interacts with abstract requirements and the current
   implementation, and how determined interfaces handle an equal
   determinant with a different dependent tuple. The current [selection
   order](../../../spec/static-semantics.md#constraint-satisfaction-and-checked-evidence)
   gives abstract and current-implementation evidence priority over lexical
   evidence; changing only the duplicate check is insufficient.
3. **Method scope and captures.** A current local method sees preceding
   bindings, not the local evidence being defined, and may close over those
   bindings. Preserve the selected identities, actual captures, their
   lifetimes and obligations. A current method's effect requests still use
   its active call context. The proposed installation-time context needs a
   rule and correspondence; ordinary closure capture alone does not establish
   how that context is supplied, and the interface itself captures nothing.
4. **Continuation access.** A current local method is a barrier to an
   enclosing resume capability. The operation's public method type and its
   implementation's access to the request-specific continuation need a
   general contract. The proposed account passes the continuation as a
   function argument with general usage and completion properties. Derive how
   elaboration constructs that argument and delimits its captured computation.

The effect catalogue gives the following completeness check for this proposed
account. The existing E rules describe current Ash; the last column records
what must be specified or established for the proposed model.

| Catalogue | Existing facts to reuse | Remaining relationship |
| --- | --- | --- |
| E1–E3 | Exact declaration and operation identities, type arguments, row and kind rules. | Relate an interface application to the exact effect requirement; preserve complete arguments even where interface evidence selection uses only determinant positions. Resolve row-parameter and scoped-evidence gaps. |
| E4 | Checked operation operand and requester-facing result type. | Relate the operation to the exact interface/effect instance and its row without assuming the method type determines every argument or selects an implementation. Carry any inferred identity explicitly into Core. |
| E5 | Checked implementation methods and handled computation. | Define installation as a scoped composition: evidence availability, the handling boundary, normal return and the exact handled and outward rows. Clause effects remain accounted for. |
| E6, E10 | Certified request, implementation, context and capture facts. | Relate a request to its applicable installed implementation and captured segment. Specify how fixed installation-time clause dependencies and nested local bindings interact with resumption; distinguish the proposed semantics from the current dynamic selection. |
| E7, E9 | Continuation input and answer types and the established contracts of captured fragments. | Connect the public operation type to the request-specific continuation and handler result. Express permitted use, scope and effects, including the remainder of a clause after resumption. |
| E8 | The applicable scoped resource and completion contracts. | Express consuming and discarding the captured control, owned and outside completion, cleanup order, effects and surviving interpreter context. An ordinary function dropping out of scope does not by itself establish those facts. |

The current one-shot rule requires each normally completing clause to consume
its continuation by resume or checked discard. A general usage property can
express that restriction without making it a property of every function.
Future multishot use and discard permission are separate contract choices;
repeatability does not establish that captured resources may be duplicated or
that cleanup can be repeated. These are design gaps, not resolved rules or an
implementation authorization.

A locally defined implementation is checked once against its interface.
Each distinct static installation or composition checks its new boundary and
relationships using the established interface, implementation and computation
contracts. It carries their scoped evidence and any unresolved obligations;
it does not recheck certified constituent bodies. Runtime activations do not
repeat type checking. Determine the source-to-Core forms and system-level
correspondence before replacing the current verification paths.

### Effect-row parameter audit

The current [row rules](../../../spec/static-semantics.md#computation-types-and-effect-rows)
define exact effect identities, substitution, lacks facts, partial union,
weakening and removal. They do not admit row binders on interfaces, their
methods or implementations. [Name resolution](../../../spec/name-resolution.md#type-binder-identity-and-scope)
likewise limits row-tail binders to globals and eligible generalized locals.
The interface well-formedness rule checks declared kinds, but does not state
the general admissible-binder restriction as an explicit premise.

The implementation admits an interface row parameter with a closed-row
implementation and uses the row in evidence selection, while method-local
and implementation row binders produce an internal compiler failure from
source. The existing [rigid-row test](../../../tests/effect_rows.rs#L405)
also exercises an interface row parameter. Reconcile these observations with
the specification; they do not establish a language rule. Any proposal to
admit additional binders must specify their scope and admissibility, row
arguments and evidence selection, substitution and lacks preservation, and
the corresponding explicit Core facts. Do not infer support for open-row
interface contracts from acceptance of one closed-row implementation.

This question arose while expressing an effectful continuation as an interface
method. The contract must be able to specify an open row for the continuation:
the continuation may use effects that are not named when the implementation
method is defined. The method must propagate those requirements to its output;
it may also have its own effects, which the output must account for. Each use
supplies a concrete row or a row bound by an enclosing context. An open row is
a bound or otherwise established row, not permission to hide unchecked effects.
Surface inference may supply the row; typed Core must carry the resulting row
and applicable evidence explicitly, including a symbolic row when it remains
open.

The implementation must be able to work with the continuation's row without
fixing it to a closed set for every use. Whether that row is bound at the
interface, method or another boundary remains to be derived. The following
complete program reproduces the closed-row interface-parameter observation;
its declaration is excluded by the current specification:

```ash
effect Ask {
    ask : Unit -> Int
}

interface Source<H, R : EffectRow> {
    get<A> : (H, Int -> A ! {| R}) -> A ! {| R}
}

type Constant = Constant(Int)

impl Source<Constant, {Ask}> {
    get (Constant(value), k) = k(value)
}

main : Unit -> Int
main () = handle ({
    let k : Int -> Int ! {Ask} = fn(n) {
        let offset = perform Ask.ask ()
        n + offset
    }
    get((Constant(42), k))
}) with Ask {
    ask ignored => resume 1
}
```

The examined compiler executes this program and reports `43 : Int`. Replacing
the implementation's `{Ask}` argument with `{}` instead produces
`constraint.unsatisfied`, so this case uses the row for selection. Two related
declarations, with corresponding `impl Source<Constant>` for the first and the
same method body for both, produced `kind.internal-state` from source:

```ash
interface Source<H> {
    get<A, R : EffectRow> : (H, Int -> A ! {| R}) -> A ! {| R}
}
```

```ash
interface Source<H, R : EffectRow> {
    get<A> : (H, Int -> A ! {| R}) -> A ! {| R}
}

impl<R : EffectRow> Source<Constant, {| R}> {
    get (Constant(value), k) = k(value)
}
```

The [interface checker](../../../src/kind.rs#L6062) admits the interface-owner
row but rejects a method-local row; the [implementation checker](../../../src/kind.rs#L6300)
rejects the implementation binder. These observations do not establish the
correct design or complete behavior for row-polymorphic evidence.

In the `Trace<A, B, R : EffectRow>` example, both tupled and curried methods
were also tested with an implementation fixed to `{}`. Both passed the
continuation's result through and evaluated to `37 : Int`. Both
`impl<R : EffectRow> Trace<Int, Int, R>` and
`impl<R : EffectRow> Trace<Int, Int, {| R}>` produced `kind.internal-state` at
the implementation's `R : EffectRow` binder. Since checking stops there,
these tests do not determine whether either row-argument spelling is accepted
after that binder is supported. Writing `R: EffectRow` inside the interface
application instead of binding it after `impl` produced `parse.expected-form`.
These observations are compiler evidence, not specification support for the
fixed or open interface-row forms. The tested method propagated `! {| R}` on
its result as well as its continuation; omitting that result row does not
account for the continuation's effects.

Supporting the required open row needs a specified and implemented account of
row binders and arguments, interface evidence selection, and their explicit
representation in typed Core. The two binder failures above identify unfinished
work; neither establishes which open-row forms should be accepted.

### Effect requirements and scoped evidence

Current Ash allows disjoint lexical scopes to provide different methods for
the same interface and local nominal type. The [scoped evidence example](../../../tests/scoped_evidence_interactions.rs#L918)
uses two `Read<Token>` implementations that return different values. A
separate [example](../../../tests/scoped_evidence_interactions.rs#L391) executes
one lexical evidence source more than once with different captured values.
These are existing interface behaviors; neither example declares an
effect-parameter requirement.

For the proposed general requirement, two occurrences of the same exact
`Failure<Token>` may therefore have different applicable `Error<Token>`
evidence in their respective scopes. The exact effect instance alone cannot
identify which evidence was established at either use. The typed interface
must preserve the relevant evidence and its scope separately from the effect
identity, together with any actual captured dependencies needed by its
contract. It must not reconstruct a selected implementation from the effect
row, merge different evidence merely because the effect arguments agree, or
change nearest-handler matching because evidence differs. Whether a use needs
only an established proposition or must transport callable method evidence is
a property of its declared contract and remains to be specified.

The general [formation and specialization candidates](first-slice-effect-completion-rules.md#effect-parameter-interface-requirements)
retain the bound and its evidence or obligation; they do not yet decide how
request and handler contracts share or separately use scoped evidence. Imports,
public summaries and Core must preserve the applicable evidence and assumptions
without exporting a local lexical source beyond its permitted scope. These are
general interface and correspondence gaps, not `Failure`-specific checks.

### Running cleanup: trace one existing check

The current [close-segment analysis](../../../src/core/capture/control.rs#L7063)
rejects a selected discard when the owned segment contains a running cleanup,
under the strict-safety or actual-capture authentication gate. An
action-local discard is not rejected merely because an action is running:
the actual owned and outside segments and their remaining obligations matter.
Separately, on a normal action return the evaluator's
[`CleanupCompletion`](../../../src/eval/machine.rs#L3392) checks `Unit` and
the live-owner counter before returning the saved body value. That runtime
finish is a different event from the earlier static discard rejection; the
one does not establish the other.

The proposed producer is the applicable general authority transition:
successful acquisition establishes the actual completion obligation, start
changes its phase to running while retaining unfinished completion and any
saved normal-body value, and capture or resume transfers that same authority
while tracking its actual placement. The new discard composition consumes
those facts and its selected-segment and outside contracts to establish that
it does not skip required work; it does not check the action again. A normal
action return can apply the finish transition only with its own `Unit`, owner
and applicable saved-value or pending-close facts. Failure, non-return and
disposal remain separate guarded cases.

The missing general evidence is a complete, scoped producer for the actual
phase, placement, action outcomes and saved-value relationship, plus the
correspondence from these facts and the authority protocol to the current
strict close check and runtime finish. It must include outside owners, unknown
actions, and the actual source/Core subject; an effect row or a `Unit` type
alone does not supply it. The separate no-error judgment also needs evidence
for the finish's possible internal failure and its preceding disposal check.
Until these relationships and all consumers are covered, the current check
remains in force. This is a contract and correspondence gap, not a new
cleanup-specific verifier.

#### Failure event during cleanup

The current [cleanup typing test](../../../tests/cleanup_typing.rs#L95)
compares a request in the protected body with the same request in its cleanup
action. An outer handler may discard the first: the action is armed, so owned
close invokes it. When the request comes from the running action, the same
outer discard is rejected as `effect.discard-unsafe`: its capture contains
the unfinished action completion. An action-local handler can instead discard
its local capture and let the action return, provided it preserves the running
owner. These examples use an operation returning `Unit`; they do not establish
an abort-only failure contract.

For the proposed abortive failure event, the same example asks how an event
from an action that has no normal reply propagates without silently abandoning
its running completion or an unfinished owned close. An ordinary default
handler has no exemption from those rules. A local handler could instead
transform the failure and allow the action to finish, but subsequent
propagation requires a suitable explicit carrier and contract; it does not
follow from returning `Unit`.

If an abortive failure is to propagate through an action, a general completion
contract must specify whether and how the action's failed outcome discharges
or transfers its invocation obligation, which resources remain open, and how
the original event and any remaining close obligations proceed. Completing an
invocation with failure does not by itself prove its resource was released.
The account must also cover a failure during a close already in progress. The
source handler selected for the original discard is removed while its clause
and owned close run, so an event from a closing action needs its own applicable
surviving interpreter; it cannot assume that the selected handler remains
installed. These are open semantic and correspondence questions, not a choice
to weaken the current completion rule or add a special default-handler rule.

### General-rule coverage and remaining design gaps

This table checks the shared rule families themselves. The linked schemas are
candidate interfaces; each gap remains a design gap even when a schema names
its required proposition. It does not add a separate derivation for each
instance or authorize removing an existing consumer.

| General rule family | Existing candidate interface | Remaining design gap |
| --- | --- | --- |
| Property introduction and use | [Shared property judgments](first-slice-judgment-requirements.md#decision-mutability-as-a-type-system-property) correlate the subject, evidence discipline and authority disposition. | Define admissible properties and their justified producers, attachment, scope and preservation, including mutability without choosing a storage or effect protocol. |
| Declaration-parameter interface requirements | The [effect formation and specialization candidates](first-slice-effect-completion-rules.md#effect-parameter-interface-requirements) carry the requirement, its scoped evidence or obligation, and its applicable authority interface; the [resource review](first-slice-resource-rules.md#resource-parameters-and-interface-requirements) identifies the same need and acquisition's distinct outputs. | Specify the shared requirement mechanism and each declaration boundary's formation, scope and Core correspondence. Current effects cannot state the bound, and Ash has no general source resource declaration. Resolve row coalescing and scoped evidence relationships; a declaration is not evidence that an implementation satisfies it. |
| Declared contract introduction and application | [Contract satisfaction, operation and handler application](first-slice-judgment-requirements.md#introduce-and-apply-declared-contracts) use the exact certified subject and carry guarded obligations. | Specify expressible contract forms, case coverage, satisfying evidence and authenticated instantiation. A signature or row alone does not prove a behavioral contract. |
| Authority and control | [Protocol-parametric transition and sequencing](first-slice-judgment-requirements.md#apply-an-authority-protocol) retain case-indexed capabilities and outcomes. [Open-residual composition](first-slice-request-capture-judgments.md#extend-an-open-residual-through-a-new-context) states a conditional pass case through one new frame. | Define protocol-specific introduction, movement and discharge and their complete scoped residuals, including future policies. Establish initial residual producers and the composed case's full correspondence; a reusable fact does not duplicate authority. |
| Facts, dependencies and resource boundaries | [Fact preservation](first-slice-facts-and-obligations.md#preserve-an-established-fact-across-a-transition), [dependency covers](first-slice-dependency-cover-rules.md#introduction-and-weakening) and [resource composition](first-slice-resource-rules.md#common-resource-judgments-and-concrete-instances) consume established facts. Cover composition and transport retain conditional source and equality obligations. | Establish subject- and state-correlated producers, complete applicable domains and declared boundary conditions. Unknown dependencies or unproved stability remain obligations; an unindexed consumer requires its premises to have been established in its context. |
| Failure and sequential cases | [Sequential failure composition](first-slice-failure-judgments.md#compose-failure-covers-in-sequence) carries phase, disposal and no-post cases. [No-error composition](first-slice-failure-judgments.md#reuse-no-error-facts-for-an-in-slice-constructor) retains the obligations of reused conditional certificates and the new composition. | Specify complete failure/observation contracts and permitted external assumptions, with sound case coverage and unbounded-residual treatment. Missing evidence is not proof of an impossible failure, and conditional safety is not a closed no-error certificate. |
| Certified reuse and Core | [Certified use and source-to-Core correspondence](first-slice-judgment-requirements.md#use-an-established-judgment) preserve scoped assumptions and obligations. | Specify how the complete resulting types and behavioral evidence are represented, transported and consumed, and justify source/Core correspondence without rechecking certified fragments. |

### Design gap: express and check mutability

Current Ash can express mutable **state through the existing cell API**, not
declare an ordinary variable mutable. The [source binding grammar](../../../spec/syntax.md#grammar)
uses `let` and a pattern; the [binding semantics](../../../spec/dynamic-semantics.md#bindings)
evaluates the initializer and extends an environment. Ordinary heap locations
are not source-level observable mutation. The [generic-cell contract](../../../spec/static-semantics.md#generic-cell-foundation)
instead provides an opaque access type, provider evidence and explicit
effectful read/write operations under the current separately owned cell scope.
`T` describes the cell's payload; writing `T`, an ordinary binding, an effect
row or an interface requirement alone does not declare a mutable variable.
Earlier [mutable-surface discussion](../DN-0043-shorter-surface-alternatives.md#resource-access-and-mutable-payloads)
is exploratory and is not current syntax or an accepted mutability model.

For the intended direction, the general type system must be able to state and
check the mutability property associated with ordinary type `T`, alongside
any applicable location and usage properties, and express the operation and
authority facts needed to use it. Mutability is not itself a new resource,
owner or per-cell verifier. Whether the property attaches to a binding, value
or access and whether its representation is a type, proposition or another
checked form remain open. Surface information may be written or inferred; no
syntax or implementation is selected here. The design must resolve, at minimum:

- **Introduction and scope:** how a mutable state subject is declared or
  inferred, associated with `T`, initialized or otherwise established and
  made available at its permitted boundaries, with complete typed Core
  information.
- **Access and aliasing:** how reading, replacing and sharing are
  distinguished; which aliases and captures denote the same state; and what
  permission, if any, is required for each operation. The design must not
  assume a particular linear, affine, borrowing or unrestricted policy.
- **Effects and control:** how actual reads and writes compose with applicable
  effect rows, declared operation contracts, handler selection, capture and
  resumption, including the distinction between an intercepted operation and
  an actual state update where interception applies.
- **Values and dependencies:** how the current value, a prior read snapshot,
  a replacement and their actual dependencies are related, including the
  treatment of the replaced value and any applicable disposal obligation.
- **Resource boundary:** which existing resource contract supplies storage,
  allocation, lifetime and disposal, and which facts make the variable's
  uses valid. The direction is no second cell-specific owner or completion
  protocol; it does not settle the resource's own policy or expand the slice
  to implement regions or arenas.

These are **design gaps**, not features already expressible or permission to
remove the current cell. Compare the current builtin's separate owner,
interception, retention, snapshot and failure behavior with the eventual
general mutable-state and resource contracts. Record any required semantic
change and every affected consumer before deciding the legacy disposition.
Do not infer semantic equivalence from matching payload types or merely
reimplement the current cell as a hidden second owner.

### Current cell behavior as evidence for the general property

The following is a before/after comparison to guide the design, not a claim
that every mutable subject has the current cell's behavior. The after column
identifies facts the shared language and applicable contracts must be able to
express **if** the intended replacement is to account for that behavior;
the semantic comparison may instead identify an explicit change.

| Current generic-cell behavior | General property and contract evidence needed |
| --- | --- |
| A [read](../../../spec/dynamic-semantics.md#scoped-cell-execution) returns the current ordinary value, preserving shared aggregate identity. A later replacement does not change the earlier result, but the snapshot does not freeze mutable cells reachable through it. | Relate the actual subject and state to the returned value and its own dependencies. Distinguish the previous result from the current stored value and preserve only the properties the applicable transition establishes. The ordinary type `T` alone does not imply copying, borrowing or a deep freeze. |
| A selected builtin write replaces that activation's current root with a checked `T`. A nearer exact handler can intercept: its reply and any clause or resumed writes determine the actual behavior; interception alone performs no builtin replacement. | Correlate actual selection, operand, subject, state transition and reply. Apply the applicable general operation and control contracts; neither mutability nor an effect-row entry proves a write happened. |
| Current `R` denotes a distinct scoped cell owner, not a storage region. Copied access refers to that owner; a live-reader closure cannot outlive it, while an independent earlier snapshot may escape. Capture moves the owned scope and resume restores it. See the [static](../../../spec/static-semantics.md#generic-cell-foundation) and [dynamic](../../../spec/dynamic-semantics.md#scoped-cell-execution) rules. | Compose the mutability and actual access/dependency facts with the applicable resource lifetime and control disposition. Determine which current relationships are supplied by the chosen resource boundary and which need further general facts; do not infer a second owner or extend a resource lifetime from mutability. |
| Write preparation can fail before replacement, leaving the root unchanged even though operand effects already happened. Disposal of the replaced last-owned value can fail after the root changed, terminating with incomplete teardown. | Preserve phase-indexed state, prior effects, failure observations and applicable disposal obligations in the general failure contract. A preparation failure is not a rollback of earlier effects, and a post-replacement failure is not evidence that the old root remains. |

The missing producers, scope and source-to-Core correspondence for these
facts remain design gaps. Reuse established property and resource evidence at
each composition; do not reconstruct the same subject's proof or introduce a
cell-specific verifier. This comparison does not choose an aliasing policy,
effect protocol, resource implementation or source syntax.

### Reuse an existing cover at a completion boundary

The unknown-value and completion entries do not yet justify adding another
specialized rule. The existing candidate interfaces already express the
following **conditional** derivation for one actual normal result and the
same resource activation:

1. The value's certified producer supplies `Cover(v,S,D)` for the relevant
   domain, or its established `Sources` relationship and member covers give
   that upper bound through the [shared cover composition](first-slice-dependency-cover-rules.md#introduction-and-weakening).
   A symbolic input without a more precise contract can use the top bound
   `Cover(v,S,S)`; it cannot use an empty bound merely because the current
   graph reports no known owner.
2. A correlated return or selected-field judgment can transport the cover to
   the **same actual value** without inspecting it again. Across an
   intervening transition, the general
   [fact-preservation rule](first-slice-facts-and-obligations.md#preserve-an-established-fact-across-a-transition)
   additionally requires a certified stability implication for that value,
   its metadata and the same states; type equality alone is insufficient.
3. If the declared boundary contract requires independence from an actual
   owner `a`, the existing [cover elimination](first-slice-dependency-cover-rules.md#independence-retention-and-predecessor-facts)
   obtains it only when `a` is in `S` and proved absent from `D`. The shared
   [resource crossing](first-slice-resource-rules.md#common-resource-judgments-and-concrete-instances)
   composition applies the specific contract's own conditions. Other resource
   contracts need not impose this independence requirement.
4. The [same shared resource interface](first-slice-resource-rules.md#common-resource-judgments-and-concrete-instances)
   composes the applicable completion contract, owner or capability
   disposition, outside obligations and guarded outcomes. The value's cover
   is one input where required; it does not prove that completion is safe,
   happens, or terminates. A later action and its transitions need their own
   certified preservation, effect and failure facts.

For the concrete unknown-only value in the audit, the top bound still includes
`a`, so step 3 cannot discharge independence. A separately established
pre-birth or other relationship can prove the needed exclusion for that same
value and dynamic activation; without it, the crossing remains an obligation,
not a proven violation or a license to repeat the producer's check. The
existing cover record defines its domain for cell-resource owners; extending
that meaning to any other dependency domain needs that domain's own contract
and correspondence, not an assumption that all resources share cell rules.
Excluded resource families remain outside this slice.

This is a reuse trace, not a completed replacement. The general representation
and producer of a complete boundary cover, the declared crossing and completion
contracts, stability through relevant control transitions, and correspondence
with current graph and phase checks remain **design gaps**. No extra
cell-specific typechecking algorithm follows from this example.

The ledger tracks logical and implementation gaps separately from the
system-level soundness and correspondence proofs. The latter justify the
rules as a whole; they are not proofs performed afresh by the compiler for
each program. Additional specialized detail belongs in an existing audit or
ledger entry when it identifies a real missing generic form, producer,
consumer or correspondence—not in a new specialized checking algorithm.

## Existing catalogue correspondence

| Catalogue family | Candidate account | Remaining rule or evidence gap |
| --- | --- | --- |
| E1–E3: declarations, instances and rows | [Effect declarations and rows](first-slice-effect-completion-rules.md#declarations-instances-and-rows-e1e3) reuse authenticated identities, kinds and existing partial row operations. A [finite closed-row derivation](first-slice-effect-completion-rules.md#a-finite-closed-row-least-union) produces leastness within the closed ground comparison domain. | Establish the retained interface and its correspondence to every in-slice consumer. Open and polymorphic rows, broader leastness and recursive row relationships need separate evidence; the candidate does not choose a new row solver. |
| E4: request | [Request introduction](first-slice-request-sequencing-judgments.md#candidate-rule-introduce-a-request), [normal return](first-slice-normal-return-judgments.md) and [request sequencing](first-slice-request-sequencing-judgments.md#candidate-rule-carry-a-request-through-a-binding) preserve the operand and saved instantiation. [Entry and port rules](first-slice-behavior-coverage-rules.md#enter-a-new-expression) include requests in the operand. | Establish a checkable, covering interface and residual compatibility for each applicable context; unknown ports and request-transition failures stay conditional without rechecking constituents. |
| E5: handler admission | [Handler composition and finite coverage](first-slice-effect-completion-rules.md#request-and-handler-admission-e4e5) separate ordinary clause checking from conditional capture-dependent facts and combine established case covers; [outcome rules](first-slice-behavior-coverage-rules.md#handler-composition) distinguish selection, forwarding and the local clause boundary. | Establish the input covers and complete handled, forwarded, clause, unknown, failure and no-reply cases for the actual subject. A named behavior constructor does not prove coverage. |
| E6 and E10: selection and capture | [Nearest boundary](first-slice-nearest-boundary-judgments.md), [selection and capture](first-slice-effect-completion-rules.md#selection-and-owned-capture-e6-and-e10) and [control invariants](first-slice-effect-completion-rules.md#control-facts-for-malformed-handler-checks) preserve exact identities, dynamic contexts, capture ownership and frame accounting. | Establish complete context and request contracts, dynamic nearest-owner preservation, actual payload crossings and all relevant conditional selections, including opaque behavior. The [residual producer gap](first-slice-request-capture-judgments.md#general-residual-interface-remaining-producer-gap) requires a correlated delimited interface that later compositions can extend without reopening a constituent. |
| E7 and E9: resume and one-shot use | [Structural usage](first-slice-continuation-use-trace.md#candidate-usage-judgments), [resume composition](first-slice-effect-completion-rules.md#resume-and-structural-usage-e7-and-e9) and [delimited ports](first-slice-behavior-coverage-rules.md#constructor-specific-delimited-ports) relate the same owner, capture and clause continuation. Successful restoration can reuse the original capture's certified port. | Establish complete port coverage and applicable external contracts, and justify the rules against the operational steps. Establish no-capture facts at opaque barriers. |
| E8: discard | [Owned discard](first-slice-close-rules.md#dependencies-and-the-discard-composition) combines the owned plan, preserved completion, interpretation, dependencies and close row. [Completion-site and route rules](first-slice-close-derivation-rules.md#introduce-references-to-pending-completion) expose pending uses and check the close before surviving control; [ticket rules](first-slice-close-derivation-rules.md#produce-and-transport-tickets-through-owned-close) track owner transitions. | Establish complete site, outside-owner and close-behavior interfaces for each covered selection. A scheduled close does not prove the action returns. |
| R1–R2: cell scopes | [Cell scope and rows](first-slice-resource-rules.md#resolve-the-scopes-type-and-row-premises) use the fixed generic payload and define proven-present and proven-absent row cases. The [closed-row correspondence](first-slice-resource-rules.md#closed-row-missing-under-a-successful-resource-scope) establishes absence under additional successful scope and substitution premises. | Reconcile current specification wording, justify conditional equality and open-tail behavior, and establish conditional body-entry facts. Structural `Missing` alone does not establish the candidate semantic absence premise; trace remaining reachable cases and specialization. Legacy removal remains a proposal. |
| R3 and R5: cell access and contents | [Acquisition and access](first-slice-resource-rules.md#r3-and-r5-acquire-select-read-and-write) distinguish actual targets, roots, read snapshots, retained values and source interception. [Dependency producers](first-slice-dependency-cover-rules.md#focused-predecessor-producer-and-consumer-correspondence) introduce correlated prebirth and retention facts; [owner and authentication judgments](first-slice-resource-rules.md#ownership-facts-for-cell-and-cleanup-control-checks) connect exact targets to runtime checks. | Establish correspondence to the current focused predecessor check, including incomplete traversal, and cover all feasible replacements and activations. May-set overlap alone is not an actual-owner proof. |
| R4: dependency and escape | [Crossing](first-slice-resource-rules.md#r4-actual-result-and-payload-crossing) checks the actual result or payload against each owner it crosses; [cover rules](first-slice-dependency-cover-rules.md) introduce and compose scoped upper bounds. | Establish the relevant opaque boundary's source facts and cover completeness; an unlisted dependency or ordinary type alone is not evidence of independence. |
| R6: capture and cell completion | [Cell completion](first-slice-resource-rules.md#r6-capture-restore-and-completion) preserves the same activation and schedules the close of an owned cell. | Derive capture/restore and outside-completion relationships from the certified control contracts; release is conditional on successful completion. |
| R7–R8: cleanup owner | [Cleanup scope and completion](first-slice-close-rules.md#introduce-and-complete-one-cleanup-owner) and [owner accounting](first-slice-resource-rules.md#ownership-facts-for-cell-and-cleanup-control-checks) distinguish acquisition, armed and running phases and preserve the saved body value. | Establish initializer-to-owner and action-entry compatibility, phase preservation, and the effect of actual action requests without reopening the action. |
| R9: cleanup interpretation | [Action context](first-slice-close-rules.md#interpret-each-action-and-compute-its-row) checks selected or outward request cases at each structural position. | Establish complete transitive request and context coverage, matching, compatibility and crossing facts, including contracts for excluded boundaries. |
| R10: close effects and dependencies | [Close rows and dependencies](first-slice-close-rules.md#dependencies-and-the-discard-composition) compose ordered owned plans and retain action, result and payload dependencies. [Derivation rules](first-slice-close-derivation-rules.md) develop plans, routes, interpreter facts, guarded row removal and a finite stationary recursive-row construction. A [ranked rule](first-slice-close-derivation-rules.md#bound-a-nonstationary-recursive-case) covers a complete finite family of changing cases with decreasing dependencies; a [row proposition](first-slice-close-derivation-rules.md#retain-the-open-row-relationship) retains the relation for an unknown tail. | Establish complete certified input plans, tickets, routes and request cases; justify and specify the row proposition, producers for ranked families, other nonstationary recursive constraints and agreement across cases. The candidate known-absent test is stricter than current structural exact removal and needs correspondence analysis. |

The [sequencing cases](first-slice-sequencing-cases.md) connect a normal
initializer result to the established remainder and preserve request,
non-return, failure and unknown alternatives. Failure disposal still needs
its own covered behavior. More generally, current internal capacity,
preparation and disposal failures have not been reconciled with the intended
narrow no-error guarantee. The [failure judgment](first-slice-failure-judgments.md)
records the agreed design: reject or retain an obligation when an internal
failure cannot be ruled out; changing the runtime response is a separate
alternative. Its ordered phase rules and handler, resource and cleanup tables
now derive specific preparation, state-change, work and capacity cases. They
still need complete storage, instantiation, control and disposal relations
and a coverage justification; an unknown failure cannot be silently discarded.
Soundness and correctness of the eventual system
are separate proof obligations; compilation checks particular programs against
the rules and does not perform those system-level proofs.

The shared value/control analysis and Core validator have consumers beyond any
single row above. The audit must identify the producer, subject, assumptions and
each consumer of an established fact before a specific old check can be retired.
Checking a new composition uses its constituent certifications; it does not
verify a certified Core fragment again.
