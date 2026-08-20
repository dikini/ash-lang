# DN-0014: Finite Kinds and Promotion

- ID: `DN-0014`
- Status: exploring
- Related: [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0003: Parser Architecture](DN-0003-parser-architecture.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md), [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md)

> This design note is informative. It does not define current Ash, accept user-defined kinds, or accept promotion. Its examples are illustrative and are not current Ash syntax or semantics.

## Question

If Ash develops an explicit kind representation with nominal atomic identities, can finite nominal static domains enter primarily through declaration elaboration and semantic policy, and can restricted promotion remain optional elaboration rather than a new type-checking mechanism?

## Context and scope

State-indexed APIs can name states and modes directly in the static language. A protocol might use `Idle`, `Open`, and `Closed`; resource and continuation designs might use multiplicity or continuation modes. Modeling each alternative as an unrelated runtime type does not declare that they inhabit one closed static domain.

This note explores two downstream hypotheses:

1. A direct declaration can introduce a finite nominal static domain.
2. A compatible runtime enumeration can optionally elaborate to the same static shape.

These hypotheses depend on future type-system foundations that represent kinds as nominal atoms and arrows, conceptually `Atom(KindId) | Arrow(Kind, Kind)`, attach kinds to rigid and inference variables, and check type application by kind. In that model, `Type` can be one atomic kind rather than the only possible atom. Those foundations must be established elsewhere; this note does not treat an imported implementation assumption as current Ash truth.

The intended benefit is narrow: static names for protocol states, resource states, multiplicity modes, and continuation modes. The note does not introduce a kind-of-kinds, dependent typing, or general datatype promotion.

## Suggested design rules

### Introduce finite domains directly

> Suggested rule: A direct kind declaration introduces a fresh nominal atomic kind and a finite non-empty set of fresh nullary static constructors.

Illustratively:

```ash
kind TxState =
    Idle
    | Open
    | Closed
```

would establish `Idle : TxState`, `Open : TxState`, and `Closed : TxState`. The smallest admissible shape is a finite non-empty nominal sum of nullary constructors. Singleton domains remain allowed. Empty domains require separate evidence.

Initially excluded shapes include constructor payloads, parameters, recursion, and arbitrary static expressions in alternatives. Those shapes bring separate questions about parameterized kinds, higher-kinded constructors, normalization, static application, type-level recursion, kind polymorphism, and static pattern matching.

### Avoid a kind-of-kinds requirement

> Suggested rule: Treat a declared domain as an atomic kind without requiring an object-language judgment such as `TxState : Kind`.

Introducing a static domain does not by itself justify a first-class universe of kinds. An implementation may allocate a nominal kind identity and register its constructors without extending the surface language with another universe level.

### Keep static constructors static

> Suggested rule: A constructor introduced by a direct kind declaration is a type-level term and need not have a corresponding runtime value.

`Open` may appear as an index where `TxState` is expected. A direct kind declaration should not manufacture runtime values merely to lift them back into the static language.

### Preserve nominal identity

> Suggested rule: Independently declared finite kinds are distinct even when their alternatives have the same spellings or shapes.

For example, `FileState` and `SocketState` remain different domains even if both declare `Open` and `Closed`. Static equality is constructor identity: the same constructor equals itself, and distinct constructors do not. Repeated source spellings are a name-resolution question, not evidence of shared semantic identity.

### Extend quantification explicitly

> Suggested rule: Allow variables to carry a user-defined kind without thereby adding abstraction over arbitrary kinds, and relax quantification policy only where a concrete use requires it.

An inference variable of kind `TxState` may solve to `Open` but not to a type of kind `Type`; a rigid variable of kind `TxState` remains rigid. A type constructor may accept a `TxState` argument using the ordinary kind-application rule.

Quantifying `S : TxState` is not the same capability as quantifying over `K` and then over `X : K`. User-defined kinds add static domains. Kind polymorphism abstracts over domains and remains a separate question.

### Make direct declaration semantic and promotion elaborative

> Suggested rule: Direct kind declaration is the semantic candidate; promotion may only derive a static domain that the direct declaration rules could already express.

Illustratively:

```ash
type TxState =
    Idle
    | Open
    | Closed

promote TxState
```

could derive the same usable static shape as the direct `kind` declaration. Initially, promotion is admissible only for a finite non-empty nominal sum whose constructors are all nullary. A parameterized or recursive datatype, a constructor with a payload, or an arbitrary runtime value is not promotable.

This restriction preserves the invariant that promotion changes convenience, not static expressivity. It does not imply that every type becomes a kind, every value constructor is lifted, constructor payloads or recursion are lifted, or every runtime value gains a type-level representation.

### Keep runtime and static identity distinguishable

> Suggested rule: Promotion establishes correspondence between runtime and static alternatives without initially requiring reflection, reification, or one shared compiler identity.

A promoted `Open` may denote a runtime constructor in term position and a related static constructor in a type position. Whether those are two identities linked by metadata or two roles of one declaration remains an experimental question. The choice must support clear name resolution and diagnostics before it supports hypothetical reflection.

## Candidate directions

### Static-domain declaration

- A dedicated `kind K = C1 | ... | Cn` declaration is the leading semantic candidate because it introduces exactly the intended static objects.
- An alternative surface form could avoid the word `kind`, but it must retain nominal identity, a closed finite inhabitant set, and static-only constructors.
- Encoding each state as an ordinary nominal type remains a baseline. It uses one declaration per state and does not declare a shared closed domain, so domain-membership constraints and related diagnostics must come from separate machinery.

### Promotion request

- A separate `promote T` declaration makes the elaboration step explicit.
- An annotation on the runtime type declaration keeps related declarations together.
- Omitting promotion initially keeps the semantic foundation smaller while direct kinds gather evidence.

All three promotion choices must preserve the same admissibility rule and must not expand the type language.

### Names and qualification

- Contextual resolution may allow runtime and static constructors to share spelling in their respective term and type positions.
- Qualification such as `TxState.Open` may be available or required.
- Explicit promoted spelling such as `#Open` may make the level visible at the cost of extra syntax.

A conservative declaration namespace can reject unrelated `type State` and `kind State` declarations while allowing an intentional promoted relationship to share its source name.

### Promotion identity

- Runtime and static constructors may have distinct identities connected by promotion metadata.
- One declaration identity may support two roles selected by context.

The first isolates runtime and static semantics; the second may simplify correspondence. Neither should be selected before namespace, diagnostic, and any real reflection requirements are tested.

## Interactions

### Type checking

The expected initial work is declaration elaboration, environment population, name resolution, and policy changes. If the prerequisite type representation exists, kind checking can accept another nominal atom, variables can retain their existing kind field, unification can preserve kinds, and type application can keep its ordinary kind-directed rule. The hypothesis fails if the basic feature requires higher-order unification, dependent checking, or type-level evaluation.

Promotion can resolve and inspect a runtime declaration, check admissibility, derive the kind and static constructors, and record correspondence metadata during declaration elaboration. The ordinary kind checker should not need to know whether an atomic kind was written directly or derived.

### Static reasoning

A finite closed declaration gives complete inhabitant information and nominal equality without reduction. Future static exhaustiveness or pattern matching could use that information, but neither is required initially. Knowing `S : State` does not imply dependent elimination or arbitrary type computation over `S`; transition relations can instead use interfaces, associated types, or explicit evidence.

### Protocols and resources

Finite kinds can give a state-indexed API a named closed domain and can name resource, multiplicity, or continuation modes. They solve naming and indexing, not stale endpoint reuse, cleanup, duplication, or other usage-discipline problems. [DN-0013](DN-0013-session-and-resource-protocol-stress-tests.md) supplies those harder tests and must not be treated as justification for privileged session syntax.

A continuation design should not assume that one finite domain captures every
control property. Usage, escape, and handler replayability are independent
enough to require separate indices, evidence, or intrinsic checking rules. A
finite kind may let a continuation type state a mode such as one-shot, but the
usage analysis must reject a second resumption and account for discard, while
the operational semantics defines what resumption and discard do.

The mechanism also must not decide whether multiplicity is an ordinary index or intrinsic type-system machinery. It only provides a finite domain when indexing is appropriate.

### Namespaces and diagnostics

The implementation must distinguish declaration-name collisions from the intentional relationship created by promotion. Diagnostics should identify the actual restriction—for example, a payload-bearing constructor that makes a type ineligible—rather than call the source declaration malformed in general.

### Feature boundaries

The design keeps four jobs separate: direct declaration introduces a static domain; promotion derives that domain from compatible runtime data; kind checking validates its use; and relations or associated types describe transitions over it. In particular, user-defined kinds do not imply kind polymorphism, promotion does not imply dependent typing, and finite domains do not imply general type-level computation.

## Evidence and experiments

A prototype, if needed, should be limited to the comparison matrix and measurements below and should compare direct declaration and promotion through one internal static representation. It is disposable and must not become product architecture without a later decision or semantic proposal and an authorized task.

The evidence must include:

| Case | Success observation | Failure observation |
| --- | --- | --- |
| Direct finite kind | A finite declaration allocates one nominal kind and the declared nullary static constructors. | Constructors leak into runtime semantics or lack the declared kind. |
| Kind-directed application | A constructor of the expected finite kind is accepted as an index. | A term of `Type` or another finite kind is accepted at the same position. |
| Inference variable solving | An inference variable solves only to a static term of its recorded kind. | It solves across kind boundaries. |
| Rigid variables | A bound variable of the finite kind remains rigid under checking. | Checking substitutes it as though it were an inference variable. |
| Nominal distinction | Structurally identical declarations remain non-interchangeable. | Matching constructor spellings collapse independent domains. |
| Promotion success | A compatible enumeration produces the same usable static shape as its direct declaration. | Promotion creates extra static expressivity or a divergent checker path. |
| Promotion failure | Payload, parameterized, recursive, empty, or otherwise inadmissible shapes receive precise diagnostics. | General datatype lifting occurs implicitly or errors hide the violated restriction. |
| Session-state example | A small state-indexed API uses finite-kind constructors as indices and kind-checks without session-specific rules. | The example needs privileged protocol handling merely to name or apply states. |
| Namespace diagnostics | Collisions and ambiguous shared spellings resolve predictably or produce actionable errors. | Resolution silently chooses a level or unrelated declarations shadow one another unpredictably. |

The prototype should also measure whether direct and promoted declarations share elaboration output, how much checker code changes, where quantification policy is relaxed, and whether removing promotion leaves every static example expressible through direct declaration.

Retain the prototype only as current design evidence if it demonstrates nominal isolation, kind-preserving solving and application, explicit quantification policy, one elaborated representation, and useful errors for every excluded shape. Discard it if prerequisite kind machinery is not established or if the experiment begins deciding general type-level computation.

## Non-goals

The initial candidate does not require:

- kind polymorphism or higher-rank kind polymorphism;
- parameterized user-defined kinds;
- payload-bearing kind constructors;
- recursive static data;
- general datatype or arbitrary-value promotion;
- type-level lambdas or pattern matching;
- dependent elimination or full dependent typing;
- singleton synthesis;
- automatic reflection or reification.

Each is an independent design question that needs concrete pressure.

## Open questions

- What declaration syntax should introduce a finite static domain?
- Should promotion use a separate declaration, an annotation on the type, or no initial surface feature?
- Should runtime and promoted static constructors share source spelling?
- Should qualification such as `State.Open` be available or required?
- May unrelated type and kind declarations share a declaration name?
- Are runtime and static constructors separate identities linked by metadata or two roles of one identity?
- Should finite kinds eventually permit zero inhabitants?
- Which concrete use would justify payload constructors, parameters, or recursion?

The main compiler-facing hypothesis is that nominal finite kinds with nullary static constructors can give state-indexed designs named closed domains and kind-specific mismatch diagnostics while optional restricted promotion remains declaration elaboration. Whether those surface names and diagnostics make the APIs easier for people to understand is a separate human-factors hypothesis that compiler experiments cannot establish. The compiler-facing hypothesis survives only if the core notions of kind, type application, variables, and unification remain intact and the unresolved cost stays concentrated in declarations, namespaces, correspondence, and diagnostics.
