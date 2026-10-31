# DN-0032: Algebra of Scoped Resource Composition

- ID: `DN-0032`
- Status: exploring
- Related: [DN-0031](DN-0031-resource-composition-concept-map.md), [DN-0009](DN-0009-effects-handlers-and-continuations.md), [DN-0010](DN-0010-identities-and-resource-lifetimes.md), [DN-0013](DN-0013-session-and-resource-protocol-stress-tests.md), [DN-0055](DN-0055-algebra-of-regions-lifetimes-and-ownership.md)

> This is a candidate algebra, not current Ash semantics or an accepted
> architecture. The equations below distinguish definitions, bounded
> derivations, and proof obligations. No complete type-safety or compiler
> correctness theorem is claimed. No implementation is authorized.

## Question and result

Can named resource provisions and supplied computations compose through ordinary
binding and sequencing, with lifetime transformations justified by laws?

[DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md) develops a
direct operational candidate for this question. It uses existing Core sequencing,
an ordered interpretation stack, and separately checked continuation capabilities.
Its rules require no computation wrappers, selectable monadic binds, or
conversions between computation models. The algebra below remains comparison
material; its computation notation does not prescribe Ash source or Core syntax.

The proposed foundation is a lambda calculus of computations with named effect
instances, parameterized theories for scopes, and a substructural account of
ownership. Its central construction is:

```text
resource contexts compose by ordered concatenation
computation bodies compose by bind
resource/body pairs compose by lifting both bodies into the combined context
```

This derives the intended `A[A'] · B[B'] = (A,B)[A';B']` for open, compatible
resource expressions. It does not identify that operator with running and
closing two scopes separately. Equivalence of such execution schedules is a
further theorem, illustrated below.

[DN-0055](DN-0055-algebra-of-regions-lifetimes-and-ownership.md) explores a
region, lifetime, and ownership algebra. It separates storage placement and
reclamation from the context product and lifetime envelope used here; these
composition laws do not by themselves merge regions or transfer their owners.

## Literature and transfer boundaries

| Source | Structure used here | What is not imported |
| --- | --- | --- |
| Plotkin and Pretnar, [Handling Algebraic Effects](https://arxiv.org/html/1312.1399), sections 2, 4–5 | Operations and equations; an interpretation must respect the theory; handling applies that interpretation. | Arbitrary handlers do not automatically preserve equations or distribute over sequencing. |
| Matache, Lindley, Moss, Staton, Wu and Yang, [Scoped Effects, Scoped Operations, and Parameterized Algebraic Theories](https://www.cs.ox.ac.uk/people/samuel.staton/papers/2025toplas.pdf), sections 2.3, 3–4 | Separate computation variables and scope parameters; binding substitution; ordered linear parameters for well-bracketed scopes. | Their scope parameters are not ordinary cell handles. Their model's unrestricted computation variables do not justify copying Ash closures that retain obligations. |
| Atkey, [Parameterised Notions of Computation](https://bentnib.org/paramnotions-jfp.pdf), sections 2, 4–5 | Computations indexed by input/output resource descriptions; sequencing and lifting through additional context. | No global store, universal symmetric resource product, or complete model of the combined Ash proposal is assumed. |
| Benton, [A Mixed Linear and Non-Linear Logic](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-352.html) | Separate reusable values from restricted authority; usage-sensitive function abstraction. | Linearity alone supplies neither scope escape checking nor effectful destruction. |
| Wadler, [Propositions as Sessions](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf), section 2 and Figure 2 | Binding, typed connection by cut, substitution, and scope movement under freshness conditions. | No claim that sequential composition is parallel composition, or that resource types are session types. Deadlock freedom does not transfer. |

The adaptation and composition derivation below are this note's synthesis.
These sources do not prove the combined system proposed here.

## Roles, types and names

An **effect theory** `E = (Sigma, Laws)` gives typed operations and equations.
For example, `read : Unit -> Int` is a signature entry; a read/write equation
is additional meaning. Two implementations of the signature need not satisfy
the same laws.

A **provider** supplies an interpretation of a theory, possibly in another
effectful computation model, and evidence for the laws it claims. A **handler**
applies that interpretation at a lexical boundary. A **resource provision**
binds a named capability to a provider under such a boundary. It need not own
mutable state or require physical allocation. These are proposed roles, not new
primitive declarations.

Use `r : E` for a formal resource slot and `r.op(v)` for a request. An exact
effect requirement is `E@r`. A provider environment binds slots, for example
`rho = (r -> P, s -> Q)`. An installed scope may introduce a fresh instance
name `a`; its runtime realization is distinct from the source spelling `r`.
Names are not global lookup strings. Provider implementation identity, instance
identity, and handler boundary identity remain distinct.

Ordinary data types describe operation arguments, results and access values.
If an API exposes an explicit handle, its type and `E@r` must use the same
instance identity. A provider's code can be reusable even when authority from
one installation cannot be copied.

## Binding is lambda binding

For values, use ordinary capture-avoiding substitution and call-by-value beta:

```text
(lambda x. m) v = m[v/x]
```

Here `v` is a value; this equation does not duplicate evaluation of an effectful
argument. Resource abstraction can be represented metatheoretically by a
contextual lambda, written `[r:E, s:F].m`. Its application obeys:

```text
([r:E, s:F].m) @ (a,b) = m[a/r, b/s]
```

This is illustrative binding notation, not a claim that current rank-1 Ash
expresses the abstraction. Substitution acts together on request identities,
access values/types, provider selection, effect rows and retained dependencies.
For example, `(E@r)[a/r] = E@a`. Alpha-renaming changes none of these meanings.

Typed substitutions compose: applying `theta` then `sigma` equals applying
their capture-avoiding composite. Proof: structural induction over the term,
renaming a bound name fresh before descending under it. The same induction
must cover type, row and evidence occurrences in a concrete elaboration.

Substitution of independent ownership parameters is injective unless a supplied
structural map authorizes otherwise. Passing one duplicable handle into two
access slots is different from turning one owner into two owners. This prevents
resource parameterization from quietly introducing contraction.

## Computation and usage kernel

Start with finite, sequential computations, exact named dispatch, and
resume-once interpretations. General recursion, escaping or multi-shot
continuations, concurrent processes and abnormal completion are extensions,
not covered by the bounded proofs here. Observable logging is permitted in the
model; allocation effects require the additional laws described later.

Let `Comp(D0,D1; X; epsilon)` describe a computation returning `X`, transforming
an input ownership/protocol context `D0` into `D1`, with outstanding effects
`epsilon`. The context is not a store of payload values. For an operation
retaining access, its owner's entry appears in both contexts. An explicit close
transition removes its obligation. Contexts may carry protocol information
where an API needs it; this does not make all resources stateful.

The following signatures describe sequencing. `epsilon union delta` combines
requirements, not operation schedules. Actual Ash row admissibility must still
be checked when elaborating them.

```text
return : X -> Comp(D,D; X; {})

bind : Comp(D0,D1; X; epsilon)
     -> (X -> Comp(D1,D2; Y; delta))
     -> Comp(D0,D2; Y; epsilon union delta)
```

Arrows here abbreviate usage-correct functions. A function capturing restricted
authority must have correspondingly restricted use; the display is not an
unrestricted duplication rule. The intermediate context is threaded once,
not copied between the two computations.

The kernel uses the usual typed bind equations:

```text
return x >>= f                 = f(x)
m >>= return                  = m
(m >>= f) >>= g               = m >>= (lambda x. f(x) >>= g)
```

For finite operation trees, define bind by substitution at return leaves:

```text
return x >>= f                := f(x)
op_r(v; k) >>= f              := op_r(v; lambda y. k(y) >>= f)
```

The three equations follow by induction on the tree. This gives an actual
bounded derivation rather than a new sequencing axiom. For a scoped term, bind
substitutes at the scope's outside continuation; it does not automatically put
that continuation inside the scope. Scope movement is separate.

Keep reusable value bindings separate from restricted obligations. A default
scope-owner context admits neither implicit contraction nor weakening. For
the nested-scope fragment it is ordered as well. Access handles can still be
reused while their required owner exists. Full closure escape checking must
track those dependencies; a bare split into linear and unrestricted contexts
is not enough.

Structural maps, if supported, have explicit types and laws: duplication
`R -> R tensor R`, disposal `R -> I`, and exchange
`R tensor S -> S tensor R`. Disposal can have effects and is not deletion.
Copying access does not imply any of these maps for its owner.

## Deriving composition of resources and bodies

Let `R` be an ordered context of resource parameters. `R tensor S` is
capture-avoiding concatenation of compatible contexts; `I` is empty. Fresh
slots remain distinct. This context product is associative and unital, not
assumed commutative. It is a product of requirements, not parallel execution.

For the first construction, bodies preserve the supplied owners. Write an
open fragment as `F = (R,f)`, where `f` maps input `X` to a computation returning
`Y` using the resources in `R`. Providers remain parameters of the fragment.
Applying an environment supplies them; constructing `F` does not run them.

We need left and right context liftings. `lift_S(f)` runs `f` with additional
resources `S` present and unchanged. It preserves exact dispatch and cannot
access a new slot accidentally. Its justification is a typed frame property,
not ownership weakening. For the free named-operation kernel it follows by
structural induction. For installed providers with observable establishment or
completion, the corresponding semantic lifting needs proof.

Coherent liftings preserve return and bind and agree under repeated context
extension. Under those premises define, with left-to-right `dot`:

```text
(R,f) dot (S,g)
  := (R tensor S, lambda x.
        lift_S(f)(x) >>= lift_R(g))

identity_X := (I, lambda x. return x)
```

Left/right embeddings keep the order `R tensor S`; `lift_R(g)` here puts the
extra `R` before `S`, not after it. The output type of `f` must match the input
of `g`. Both computations' rows are embedded into the combined context and
combined. This is precisely resource-context composition plus continuation
substitution. Ignoring explicit input/result binders gives:

```text
A[A'] dot B[B'] = (A,B)[A';B']
```

Associativity is derivable. In a common context `R tensor S tensor T`, the two
parenthesizations have the same provider parameters in the same order and
bodies:

```text
(f(x) >>= g) >>= h
f(x) >>= (lambda y. g(y) >>= h)
```

They agree by bind associativity and coherence of the liftings. Identity
follows from the two return laws and empty-context lifting. Thus these open
fragments form a category of compatible typed computations, modulo the stated
equations and alpha-renaming. The resource contexts have an ordered monoidal
structure; this does not establish a symmetric monoidal structure on effectful
computations or an interchange law.

An independently supplied `g` does not gain free references merely through
composition. To use `R`, declare `g` under `R` as well, or pass its access as
part of `f`'s result while the composed scope owns it. Shared context entries
are threaded once, not concatenated twice. If establishing `S` depends on
`f`'s result, use indexed bind with a continuation that establishes `S`; do not
hoist that establishment into an input-independent provider tuple. The more
general `Comp(D0,D1;X;epsilon)` interface describes those transitions, but its
full scope typing is still to be supplied.

## Providers interpret; handlers delimit

For an exact instance, an interpretation acts on operation trees as follows:

```text
H_P(return x)     = ret_P(x)
H_P(op_r(v; k))   = P_op(v, lambda y. H_P(k(y)))
```

This is the deep, exact-instance case. Unmatched operations are forwarded with
their handled continuations. Provider clauses execute in their declared
interpretation context. An operation they issue is not silently routed back
into themselves. Captured owner restrictions apply to the supplied continuation.

In general `H_P` can change result and residual effect types; its contract must
say how. Resource-independent notation does not require a state representation.
For a fixed, compatible ordered environment define installation composition by
`H_(P,Q)(m) := H_P(H_Q(m))`. This is scope nesting, not a theorem about reordering.
An effect used by `Q` can be handled by enclosing `P`; the reverse dependency
requires a different arrangement. Substitution and row checking determine
whether this composition is admitted.

A law-respecting provider sends each equation of its declared theory to an
equality in its target model. That fact extends to equations derived by
congruence, substitution and transitivity, by induction on derivations. It
does not establish preservation of laws belonging to unrelated effects or
unproved interaction equations.

In particular, do not assume `H_P(m >>= k) = H_P(m) >>= (H_P composed_with k)`.
A handler can transform answers, choose branches or carry state across the
whole body. Such a distributivity law requires additional structure. The open
fragment derivation above deliberately sequences bodies before interpretation.

## Scope movement and lifetime intervals

Use `nu a.m` for pure fresh-name binding, not physical acquisition. Process
calculus scope extrusion motivates the freshness condition in a sequential
analogue: a fresh-name boundary can move across a computation that cannot
mention or observe that name. This says nothing by itself about moving a lock,
allocation, provider callback or external interaction.

For an installed provider write `S_P^a(m)` for its scoped interpretation,
including any establishment/completion behavior. Two useful equations to
prove for suitable providers and contexts are:

```text
S_P^a(m) >>= k
  ≈ S_P^a(m >>= k)                      (right extension)

m >>= (lambda x. S_Q^b(n(x)))
  ≈ S_Q^b(m >>= n)                      (left extension)
```

Right extension requires `a` absent from the support of the outside `k`.
Left extension requires `b` absent from `m` and `Q` independent of `x`. Support
includes captured values, effect identities, types and selected evidence.
Freshness prevents capture; it is not the entire proof. Both equations also
need compatible result contracts and proof that moving the interpretation's
establishment/completion does not change observable behavior. For example, a
fallible acquisition cannot generally move ahead of `m`.

When those premises hold, the closed-execution fusion equation follows:

```text
S_P^a(m) >>= (lambda x. S_Q^b(n(x)))
≈ S_P^a(m >>= (lambda x. S_Q^b(n(x))))   by right extension
≈ S_P^a(S_Q^b(m >>= n))                 by left extension inside P
```

This is the execution theorem corresponding to the open composition law. It
is conditional, with named proof steps. These freshness conditions apply to
the closed starting expression. An open composition whose later body uses
`a` directly can be well formed without having that closed decomposition.

For one dynamic execution, a scope lifetime is an interval in the execution's
event order. A composed region uses the hull of its constituent intervals.
Hull is associative and unital with the empty interval; this geometric fact
does not prove a program transformation. Retained continuation dependencies
remain within logical lifetime even while inactive. Divergence or retained
control can leave an interval without a finite endpoint.

Logical availability and physical establishment are related by realization
proofs. Their schedules can differ where observations permit. Composition
does not prescribe that all physical acquisitions happen at region entry.

## Small model, proof and counterexample

Consider immutable integer providers `P=10` and `Q=20`, with pure, total setup,
no observable completion and exact named requests. Interpret `a.ask()` as 10
and `b.ask()` as 20. Let `m = a.ask()` and
`n(x) = b.ask() >>= (lambda y. return (x+y))`.

The separate schedule obtains 10 then 20 and returns 30. The composed schedule
evaluates the same requests in the same order and returns 30. More generally,
each interpreter replaces only its exact requests by returned constants and
forwards external operations unchanged. Induction on finite computation trees
proves both extension laws under the support premises, preserving the external
trace as well as the result. This is a nonempty model of the fusion law, not
just a syntactic postulate.

Finite private cells give another bounded model if initialization is pure and
total, completion is unobservable, identities cannot escape, and no external
observer can access the cells. Relate the two executions by equal live cell
contents on all accessible names; a retained inaccessible cell contributes no
observable step. Reads and writes preserve this relation. Finite induction
proves the same result and external trace. Observable allocation failure or
allocation accounting invalidates this model's assumptions.

For a contrary case, let `P` emit `close-a` on completion and let `k` emit `b`.
Separate execution emits `close-a, b`; right extension emits `b, close-a`.
Even though `k` has no reference to `a`, the equation fails under ordered trace
observation. Likewise, moving `Q` before `m` fails if acquiring `Q` fails before
an event that `m` would otherwise emit. Types and provider-law proofs must
establish the required premises; no separate unsafe-composition annotation is
introduced by this algebra.

## Correctness and measurement

Use three different relations: alpha/definitional equality for binding and
construction; theory equality for derivable provider laws; contextual
equivalence for observable execution. Do not equate them without a soundness
theorem. Observation includes returned values, termination/failure and external
traces, extended with identity or timing observations when the contract exposes
them. With nondeterminism, trace sets alone may be insufficient; a suitable
contextual or bisimulation model must be selected.

| Obligation | Proof route | Present status |
| --- | --- | --- |
| Binding coherence | Induction for alpha-renaming and simultaneous substitution. | Argument given for abstract syntax; concrete Ash elaboration theorem open. |
| Body sequencing | Induction on finite return/operation trees. | Bounded derivation given. |
| Open composition identity/associativity | Bind laws plus coherent context liftings. | Conditional derivation given; free named-operation kernel supplies liftings. |
| Provider correctness | Prove defining equations in its target model, then induction on equation derivations. | General proof method; concrete provider proofs required. |
| Scope fusion | Establish extension laws, then the two-step derivation above. | Reader model proved by induction argument; private-cell simulation sketch; trace counterexample supplied. |
| Resource safety | Preservation of ownership/protocol contexts, support and unique completion authority. | Full operational semantics and subject-reduction proof remain open. |
| Capture and abandonment | Ownership transfer into continuations and compatible closing of all retained obligations. | Existing Ash evidence is a constraint, not a proof for this extension. |
| Compiler rewrite | Contextual simulation or a proved equation with instantiated premises. | No current compiler transformation claimed. |

Cost is a separate semantics: count operation dispatches and establishments,
measure peak retained owners/bytes, and record completion work. Compare costs
only after observational equivalence is established. Counts can add under
sequencing; peaks depend on interval overlap and cannot generally be added as
exact values. A composition can reduce dispatch while increasing retention.
Host guarantees remain assumptions at the provider boundary; proofs about an
external provider are relative to its stated environment model.

## Constraints, alternatives and Ash transfer

### Continuation extensions and sequencing laws

Current Ash's hidden continuation capability is nonduplicable and nonescaping;
normal clause completion consumes it through resume or checked discard
([current rules](../../spec/static-semantics.md#effects)). These are the
current admissibility conditions, not universal axioms of resource composition.
The finite resume-once fragment above bounds its proofs, not future Ash.

As explored in [DN-0009](DN-0009-effects-handlers-and-continuations.md) and
[DN-0013](DN-0013-session-and-resource-protocol-stress-tests.md), continuation
use has separate dimensions: duplication, abandonment, escape, suspension and
possibly concurrent resumption. Do not collapse them into a single linear to
multi-shot progression. A continuation may escape while still being one-shot;
multi-shot execution need not be concurrent.

The following maps theorem premises over Core. The candidate interpretation
below explores how sequencing could depend on a continuation model; neither
discussion selects a source annotation, mode kind or representation.

| Behavior under consideration | Required facts about the whole captured Core segment | Laws requiring review |
| --- | --- | --- |
| Current resume/discard | The owner moves once; discard preserves outside/running completion and closes the owned capture. | Scope movement preserves the selected owner and completion dependencies. |
| Sequential multi-shot | Every captured restricted value and owner admits the chosen duplication or sharing interpretation; requests made again have the provider's specified meaning. | Duplication, lifting and fusion preserve that interpretation and the number/order of observable operations. |
| Escaping one-shot | Referenced resources, code and selected evidence remain available; the eventual owner of completion is defined. | Lexical scope exit is no longer a sufficient physical release point. |
| Suspension | Suspended obligations remain owned; any later abandonment has a valid closing interpretation. | Lifetime bounds include inactive periods; eventual completion is not inferred. |
| Concurrent resumption | Shared access and completion synchronization satisfy provider contracts, beyond permission for sequential repetition. | Exchange, interference and concurrent observations need separate proofs. |

Multi-shot does not mean copying an existing resource owner byte for byte.
Providers may support shared access to one retained instance, independent
instances per branch, or no duplication of captures containing that provision.
These are different interpretations, not equivalent implementation choices.
Independent instances need coherent fresh-name substitution for all related
handles, operations and evidence. Shared instances retain a defined completion
owner; copying their handles does not multiply release authority. This note
selects neither policy and introduces no reference-counting requirement.

Repeated requests can intentionally repeat external effects. Such an
interpretation is not automatically invalid, but a rewrite must preserve its
specified observations. Permission to copy captured values alone proves
neither provider compatibility nor equivalence of repeated computation.

For example, a continuation that increments a cell and then reads it can
produce 1 then 2 when resumed twice with shared state, or 1 then 1 with fresh
copies initially containing zero. A scope-fusion transformation must not
change between those interpretations. If moving a resource boundary across a
capture point changes what is retained or duplicated, the existing one-shot
fusion proof does not apply even if all source names remain fresh.

Record each law's continuation assumptions with its proof. Reuse the binding
and sequencing derivations where their substitution and usage premises still
hold; re-establish operational soundness for the extended Core transitions.
Scope movement additionally preserves capture extent, identity relationships,
provider interpretation and completion multiplicity. A future extension is
conservative only if old well-typed programs retain their old observations and
old proofs remain usable under their original assumptions. This is a required
theorem, not a consequence of adding a mode label.

The interval account is also conditional on the control model. In sequential
execution, each dynamic activation can retain an interval that includes all
its uses. Branch copies have distinct activations; shared ownership relates
several uses to one owner. Under concurrency, a partial order of events and
dependency regions may be needed; one total-order hull can be a conservative
summary without being the complete semantics. No current lifetime proof is
silently generalized to these cases.

### Asynchronous effect hooks require scheduling semantics

Asynchronous hooks are another future extension boundary. Once publication
can proceed independently of subscriber completion, publisher and subscriber
work have concurrent lifetimes and require scheduling semantics. This does
not require parallel threads: interleaving on one executor still introduces
ordering, progress and ownership questions.

Current [synchronous hooks](../../spec/static-semantics.md#synchronous-typed-hooks)
interpret an exact effect API through an ordered transformer chain. Keeping
asynchronous execution, concurrency and scheduling outside Effect Ash was a
deliberate milestone boundary: [DN-0026](DN-0026-effect-ash-resource-first-milestones.md#leading-boundary)
records that boundary and its later suspension and concurrency slices.
[DN-0012](DN-0012-coeffects-and-hooks.md) supplies the broader hook exploration.
The present algebra must permit that extension without changing the meaning
of existing synchronous publication.

For asynchronous hooks, laws over Core must account for:

- the ordering of publication, subscriber selection, scheduling, execution and
  completion, including whether publication waits for any result;
- transfer or sharing of payloads and captured resource access during fan-out;
- which handler/provider context interprets subscriber effects after the
  publishing computation proceeds;
- ownership of queued and running callbacks, and what deregistration or region
  completion means while such work remains;
- failure, cancellation, joining or draining, and release of every obligation
  under the selected policy;
- the scheduler assumptions required for progress claims, including any
  fairness premise rather than an unconditional eventual-completion claim.

These are semantic questions and proof premises, not selected policies. Row
union alone establishes none of them. Scheduling a callback is not equivalent
to completing it; a scope cannot be released merely because publication has
returned if scheduled work still depends on it. A fusion proof must preserve
the permitted ordering of events and retained interpretation context, not
only the publisher's result. Use dependency regions and event partial orders
where a single sequential interval no longer expresses the obligations.

Asynchronous hooks and multi-shot continuations are independent extensions:
several subscribers can each execute once, whereas multi-shot resumes one
captured continuation repeatedly. Their interaction needs a further proof
that fan-out and replay do not duplicate restricted authority or change
completion multiplicity. A future scheduler may require additional Core
operations; that does not require replacing existing binding/sequencing or
assuming a universal scheduler in the present algebra.

### Candidate interpretation: sequencing relative to a continuation model

One plausible foundation treats Ash's implicit monadic sequencing as relative
to a continuation model. One source sequencing construct could then admit
different semantic interpretations and implementations. This is a direction
for theory and formalisation, not a claim that current Ash supports selectable
continuation contracts or that all such models satisfy the same laws.

In schematic CPS notation, the familiar construction is:

```text
return x = lambda k. k(x)
bind m f = lambda k. m(lambda x. f(x)(k))
```

These equations describe continuation composition. They leave the answer type,
delimiters, usage restrictions, resource ownership and disposal transitions
unspecified. Their shared shape does not establish that affine and multi-shot
models have identical types or observations. In a restricted model, even the
permission to construct or reuse the displayed closures needs justification.
The indexed `Comp` signature above is a starting point for stating those
conditions, not a completed typing of this CPS account.

A handler installs an interpretation boundary. A request captures the segment
through that boundary, and resumption reinstalls it. For the illustrative body
below, suppose both expressions lie inside the selected boundary:

```text
let x = perform Choose()
emit(x)
```

The captured suffix includes `emit(x)`. An interpretation that resumes once
executes that suffix once; one that resumes twice may emit twice; abandonment
skips the suffix and must account for captured completion obligations. The
prefix before capture is not repeated by resumption. This is a schematic
comparison of possible interpretations, not executable current Ash syntax.

| Contract dimension | Question for the sequencing model |
| --- | --- |
| Exactly-once use | How does the model ensure one consumption while distinguishing resumption from eventual completion? |
| Affine use | When may the suffix be abandoned, and which captured obligations must still be completed? |
| Multi-shot use | Which captures may be reused, and do repeated requests share resources or use distinct branch instances? |
| Explicit disposal | What transitions and observable effects complete an abandoned capture, and who owns their execution? |

These dimensions are not exclusive modes. In particular, disposal is distinct
from multiplicity; effectful disposal cannot be modeled as silent weakening.
Escape and suspension add the lifetime obligations described above.

Compare two formalisation routes: one computation calculus with contracts on
captured continuations, or a family of usage-sensitive or indexed computation
models with related `return` and `bind` operations. The first may preserve a
shared account of syntax and substitution; the second may expose differences
in admissible composition more directly. Neither route is selected. For each,
define typing, delimiter behavior, capture/resume/dispose transitions and
observational equivalence before proving the well-typed identity and
associativity equations. Check scope movement and lifting separately. A
handler's interpretation need not preserve bind merely because its source and
target models each have lawful bind.

Implementation variation is a further question. Stack segments, CPS closures
or another representation could implement a specified contract if they preserve
its observations and ownership rules. Changing from one resumption to repeated
resumption, or from shared to branch-local state, changes the semantic contract;
it is not an interchangeable implementation of the same behavior. A useful
comparison would first fix each model's observations, then ask which runtime
representations implement it and which laws transfer between models.

### Sequencing is already ambient in Ash

The `bind` notation in this note is a semantic description of existing Ash
sequencing, not a proposed source method, monad wrapper or additional Core
operation. The source expression below realizes `m >>= (lambda x. n)`:

```text
{
    let x = m
    n
}
```

Here `m` and `n` are metavariables for Ash expressions and `n` may use `x`.
The [binding semantics](../../spec/dynamic-semantics.md#bindings) evaluates `m`
with a frame retaining `n`, its pattern and lexical environment. Returning a
value matches it and continues with `n`. Core already contains
`PureComputation::Bind(BindingNode)` in [the shared substrate](../../src/core/dialect.rs).
Its location in the shared pure family does not make sequencing unavailable
to Effect Core. Strict application and other evaluation contexts also sequence
computations without a written `let`.

In schematic continuation notation, suppressing the heap and other machine
components, the sequencing equation is:

```text
eval(let x = m in n, env, k)
  = eval(m, env, lambda v. eval(n, env[x -> v], k))
```

This is the continuation reading of bind, not a proposed translation that must
allocate the displayed lambda. The actual abstract machine uses frames. An
ordinary value supplies the corresponding return behavior.

[Handler semantics](../../spec/dynamic-semantics.md#effect-handlers-and-completion)
delimits that control: a request selects the nearest exact interpretation,
moves the segment through that boundary into the clause's owner, and `resume`
reinstalls it. Checked `discard` closes its owned obligations. Core has
explicit request, handler, resume and discard nodes in
[the Effect family](../../src/core/effect.rs); execution is in
[the evaluator](../../src/eval/machine.rs).

Thus a delimited-continuation interpretation is a useful semantic account of
existing Core. It is not an unrestricted source `Cont` value: exact effect
identity, lexical instantiation, non-escaping continuation use and completion
ownership constrain the admissible control transformations. The continuation
equation alone neither models all of those obligations nor proves their laws.

The proposed contribution is therefore an algebra over existing scoped
computations. Body composition uses current sequencing. Resource-context
composition describes the bindings and interpretations surrounding it.
Typing and proofs establish when scope reassociation or lifetime movement
preserves that computation. General parameterized provision and the proof
interface remain missing. The current fragment needs no second source
sequencing construct; whether future continuation models share its typing,
operational rules and bind laws remains a formalisation question.

### Alternatives and reuse

The selected starting point for further study is contextual lambda abstraction
over named provisions, with ordered scope parameters and indexed sequencing.
It reuses the largest relevant literature base while retaining the user's
resource/body separation.

Compare it against two alternatives: ordinary higher-order wrappers around
current scopes, which are simpler but may not express the fresh binding and
fusion laws; and a full session-process calculus, which supplies richer
interaction protocols but adds concurrency structure not required by this
question. Neither alternative is ruled out by a theorem here.

[DN-0031](DN-0031-resource-composition-concept-map.md) remains the coverage map.
Reuse current binder identities, exact effect instances, evidence transport,
resource dependency inference and continuation ownership as constraints on an
encoding. The general provider, contextual abstraction, structural proofs and
composition laws are not thereby implemented. No new resource registry,
universal state object, proof syntax or kind is chosen in this derivation.

## Next evidence and open questions

Complete a small typed syntax and transition system before claiming soundness
of the combined calculus. The first comparison should cover two named instances,
aliases, supplied bodies with captures, dependent sequencing, and failed
establishment. Account for current owned abandonment, then compare multi-shot,
escape and suspension against the separate premises above. Keep shared versus
branch-local cells, duplicated cleanup, repeated external effects and captured
provider dependencies as positive/negative cases. No prototype is authorized here; a prototype needs a
specific question, comparison criteria and disposal/retention conditions.

The remaining design questions are how contextual parameters appear in Ash
types, how proof terms certify the lifting and extension laws, how usage and
stored dependencies compose, and which observation model covers the intended
external providers. These are gaps in the proposed system, not gaps in the
bounded algebraic derivation.
