# DN-0008: Typed Core and Elaboration

- ID: `DN-0008`
- Status: exploring
- Related: [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0002: Core Representation](DN-0002-core-representation.md), [DN-0005: Surface Function Definitions](DN-0005-surface-function-definitions.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0007: Data and Pattern Typing](DN-0007-data-and-pattern-typing.md), [DN-0017: Resource Management and Storage Policy](DN-0017-resource-management-and-storage-policy.md), [DN-0018: Runtime-Established Static Evidence](DN-0018-runtime-established-static-evidence.md)

> This design note is informative and non-normative. It explores typed Core and elaboration candidates; it does not define current Ash, accept an architecture, or require downstream capabilities. All syntax and internal forms are illustrative.

## Question

What typed Core and elaboration boundaries would make omitted surface typing operations explicit, preserve useful pattern structure, support checkable transformations and direct execution, and leave room for later static evidence or representation changes without implementing them now?

## Context and scope

[DN-0002](DN-0002-core-representation.md) asks which concrete Core representation fits a small pure language while keeping continuations inspectable and transformations checkable. This note narrows one part of that exploration: the semantic information surface elaboration should produce and the boundaries among Core forms, semantic rules, transformation mechanisms, and possible future evidence.

The scope is:

- explicit term and type abstraction and application in Core;
- elaboration of equational and operational functions;
- typed structured patterns and compiled decision forms;
- explicit Core dialect contracts;
- direct execution of each retained semantic Core form;
- centralized semantic rule boundaries;
- separation of unification, constraints, normalization, and equality;
- representational seams for later evidence passing, effects, CPS, opacity, and existentials.

This note does not choose the concrete recursive Core encoding, CPS representation, runtime layout, normative semantic notation, effect semantics, or optimizer architecture. Those questions remain open or belong to other artifacts.

## Accepted first-stratum boundaries

[AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md) accepts a
distinct binder-resolution boundary followed by bidirectional typed elaboration
to structured Core. [AD-0007](../decisions/AD-0007-typed-core-dialects.md)
accepts named typed Core dialects, independent validation, and the pure
operation-family boundary. [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)
accepts direct execution through an explicit first-order machine. They leave
the richer polymorphism, pattern-compilation, evidence, effect, CPS, storage,
and optimizer questions in this note open.

## Suggested design rules

### Make surface polymorphism explicit in Core

> Suggested rule: Surface omission of type abstraction and instantiation elaborates to explicit, typed Core operations.

An illustrative surface definition:

```ash
id : A -> A
id(x) = x
```

could elaborate conceptually to:

```text
ΛA : Type.
    fn(x : A) -> A {
        x
    }
```

A surface use such as `id(42)` could become:

```text
(id [Int])(42)
```

Core would distinguish:

```text
TermLambda
TermApply
TypeLambda
TypeApply
```

This makes polymorphic operations available to validation and transformation instead of treating elaborator omissions as semantic absence. The same ordinary binding and application structure could later carry generated evidence if such a feature is designed; no evidence system is required now.

### Elaborate function presentations to the same typed semantics

> Suggested rule: Operational bodies and equation groups produce the same typed Core constructs after surface-specific elaboration, while retaining source provenance separately.

Equation heads can elaborate through the pattern forms discussed below. A single irrefutable equation may become an ordinary lambda body without a meaningful match. The Core need not record “equational function” as a second semantic function kind.

Source maps or provenance nodes should preserve enough information to diagnose a failed clause, generated argument, or inserted type application against the programmer's source. Provenance is tooling data, not a semantic distinction.

### Preserve typed structured patterns before lowering

> Suggested rule: One Core form may retain typed structured patterns, while an explicit transformation compiles them into lower-level decision forms.

A structured form might resemble:

```text
Match {
    scrutinee
    typed pattern cases
}
```

A decision form might expose:

```text
constructor tests
field or tuple projections
bindings
branches
```

Transforms before lowering can reason directly about `Some(x)`, tuple decomposition, or labelled record patterns. Transforms after lowering can reason about tests, branch sharing, projections, and dead branches. Pattern compilation would be a typed Core-to-Core operation rather than an untracked parser side effect.

Coverage and irrefutability remain semantic checks from [DN-0007](DN-0007-data-and-pattern-typing.md); successful lowering should not redefine them.

### Give materially different Core forms explicit contracts

> Suggested rule: When two Core forms have materially different admissible nodes and useful invariants, name their dialect contracts and require transformations to declare what they consume and produce.

One candidate division is:

```text
CoreStructured
CoreDecision
```

with illustrative contracts:

```text
simplify_match : CoreStructured -> CoreStructured
compile_patterns : CoreStructured -> CoreDecision
simplify_case : CoreDecision -> CoreDecision
```

Both would remain fully typed. Dialect boundaries need not imply a mandatory chronological pipeline; they describe checked representation states. A new dialect should require evidence that its invariants materially simplify or enable transformations, otherwise micro-dialects would add validation and conversion cost without enough benefit.

### Keep every retained semantic Core dialect directly executable

> Suggested rule: Each retained Core dialect has a direct interpreter so transformations can be compared by observable evaluation.

Direct execution supports differential checks such as:

```text
evaluate(program) == evaluate(transform(program))
```

for programs whose observable result is defined by the experiment.

An interpreter candidate represents language evaluation state explicitly:

```text
Machine {
    control
    environment
    continuation
}
```

rather than relying on the host call stack as the only representation of language continuations. Explicit state would let the pure first language test evaluation order and transformation behavior while keeping continuation structure inspectable. Effects, handlers, concurrency, cancellation, and one-shot or multi-shot continuation semantics are downstream pressure only.

Direct interpretation need not make every intermediate compiler data structure a semantic dialect. The criterion is whether the form is retained as a meaningful transformation boundary whose behavior must be validated.

### Centralize semantic decisions and separate them from mechanism

> Suggested rule: Each semantic question has one authoritative rule interface that returns structured outcomes; storage and algorithmic mechanisms remain behind those rules.

Candidate rule boundaries include:

```text
TypeEqualityRule
KindCheckingRule
QuantificationRule
InstantiationRule
FunctionExposureRule
GeneralizationRule
AnnotationRequirementRule
PatternTypingRule
PatternIrrefutabilityRule
CoverageRule
RecordFieldLookupRule
AccessRule
```

Mechanisms such as union-find, substitutions, type arenas, constraint stores, and tree traversal may support several rules but should not define language policy incidentally.

Structured outcomes make policy and diagnostics visible:

```text
GeneralizationDecision =
    Generalize(vars)
    | KeepMonomorphic(reason)
    | RequiresAnnotation(reason)

CoverageDecision =
    Exhaustive
    | MissingCases(patterns)
    | RequiresCatchall(reason)
```

These interfaces are candidates for experiments, not mandatory source modules or public APIs.

### Keep constraint resolution distinct from type mechanics

> Suggested rule: Unification, constraint resolution, type normalization, and type equality remain separate operations even when the first coherent type checker needs only kind and type equality constraints.

A small initial solver could handle:

```text
type equality
kind equality
```

Possible interfaces, rows, associated types, or propositions may later add different obligations. For example, a requirement such as `Eq<A>` would state that evidence is needed; it would not itself be the evidence. A future elaboration might pass such evidence through ordinary Core type and term binders. Associated projections might introduce reducible type expressions whose normalization depends on resolved evidence.

Those examples are pressure tests only. The initial Core need not contain dictionaries, associated projections, row evidence, propositions, or proof terms. Its immediate responsibility is to avoid one recursive “solve everything” procedure that silently conflates the four semantic operations.

### Preserve extension seams without placeholder semantics

> Suggested rule: Future capabilities influence present representation only through concrete separations that can be tested now; they do not introduce unreachable placeholder constructs or current-language requirements.

Potentially useful seams include:

- explicit type binders, rigid variables, and scopes for later existential or opaque operations;
- ordinary typed term binders and applications through which generated evidence could travel;
- explicit representation-access facts rather than equating type visibility with constructor access;
- explicit continuation data for later effect and CPS experiments;
- typed dialect boundaries for possible Core-to-CPS and CPS-to-Core transforms;
- rule inputs that can accept later effect, generativity, resource, or refinement facts.

A seam is justified only if it keeps an existing responsibility clear or supports an experiment with named cases, comparison observations, and retention conditions. “Extensibility” alone is not evidence.

### Preserve established facts until their last checked use

> Suggested rule: A Core transformation retains or revalidates every static fact
> needed by a later checked transformation, then erases that fact only after its
> last consumer.

Possible future resource work could establish facts such as unique authority,
disjoint places, one-shot control, or the locality of an identity. Those facts
could justify in-place update, ownership transfer, frame reuse, or removal of an
internal effect requirement. A low-level backend need not understand the source
type mechanism, but erasure must not happen before the transformation that relies
on it.

This is a representation pressure, not acceptance of any resource discipline or
optimization. A candidate must identify the producer, validator, consumers, and
invalidation conditions for each retained fact. Attaching unchecked metadata to
Core would move the semantic decision rather than make it explicit.

## Candidate directions

### Fully explicit typed Core

This is the main candidate. It exposes type abstraction/application, term structure, pattern information, and dialect invariants to validation. It costs larger terms, more elaboration steps, and more obligations for every transform.

### Typed nodes with implicit Core polymorphism

Core nodes could carry final types while leaving instantiation and abstraction implicit. This reduces syntax and node count but makes specialization, substitution, transformation validation, and later evidence passing depend on reconstructing hidden operations.

### One Core pattern representation

Keeping only structured patterns preserves source-level meaning but forces decision-oriented transforms and execution to rediscover tests. Keeping only decision forms simplifies execution but discards useful high-level structure early. Keeping both adds a transform and two validators; experiments should show whether each side enables materially simpler work.

### Dialect granularity and conversions

[AD-0007](../decisions/AD-0007-typed-core-dialects.md) rejects one permissive
node set as the retained semantic Core boundary. The exact dialect granularity,
node-family assembly, conversion ownership, and validation evidence remain
open. Experiments should justify each additional dialect by the guarantees it
provides to consumers.

### Explicit-machine composition

[AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md) selects an
explicit first-order machine for the retained evaluator. A host-recursive
interpreter may remain a disposable differential oracle. Further comparison
should concern transition ownership, frame composition, inspectable code and
environment storage, diagnostics, and resource accounting within the accepted
machine boundary.

### Rules as functions, modules, or declarative data

Centralization does not determine implementation form. Rules could be functions with structured results, dedicated modules, tables interpreted by the checker, or another organization. The important candidate property is one reviewable decision path per semantic question.

### Direct Core-to-runtime lowering without a persistent interpreter

Lowering only to a backend may reduce duplicate execution machinery. It weakens differential testing and makes backend behavior part of every Core experiment. A minimal interpreter may be worthwhile even if it is not the production execution route.

## Interactions and architectural pressure

- [DN-0002](DN-0002-core-representation.md) owns the broader representation question, including Freer-like candidates, explicit continuations, Core/CPS relationships, and opaque CPS regions. This note provides experiments and constraints, not an answer to that question.
- [DN-0005](DN-0005-surface-function-definitions.md) requires equivalent elaboration for equation groups and operational bodies plus source provenance for form-specific diagnostics.
- [DN-0006](DN-0006-initial-type-system.md) supplies candidate kinding, instantiation, equality, generalization, recursion, and unification rules that Core must represent and revalidate.
- [DN-0007](DN-0007-data-and-pattern-typing.md) supplies typed patterns, visibility, irrefutability, and coverage obligations. Pattern compilation should preserve those established facts or revalidate their relevant consequences.
- [AD-0004](../decisions/AD-0004-small-step-semantic-method.md) selects
  small-step semantics as the primary normative method. An explicit machine can
  provide implementation evidence without becoming normative semantics.
- Possible Core/CPS movement pressures dialect interfaces not to assume one irreversible lowering pipeline. CPS reconstruction and opaque CPS regions are not requirements for the first Core.
- Possible optimization search pressures transform applicability to remain checkable and output to be revalidated. Heuristic search or ML ranking is not part of the trusted semantic core and is not an initial requirement.
- Possible interfaces, handlers, existentials, and proof evidence pressure explicit binders and applications. They should not be encoded speculatively before their semantics exist.

## Evidence and experiments

A Core experiment should be limited to the probes and comparisons listed below and remain disposable. Its provisional IR is evidence, not product architecture or language truth. Compare candidates using the same small typed programs and report representation size, validator complexity, traversal behavior, diagnostic provenance, and failure modes.

Required probes include:

- explicit global polymorphism and explicit instantiation at multiple use sites;
- local generalization whose resulting Core binder scope is inspectable;
- equivalent equational and operational definitions elaborated to comparable Core;
- parameterized ADTs and constructor values;
- nested constructor, tuple, and record patterns in structured Core;
- pattern compilation into decision Core with types and source provenance retained;
- direct execution of the structured and decision forms;
- a beta-reduction or simplification transform followed by type validation;
- differential evaluation before and after pattern compilation and simplification;
- invalid Core containing a scope error, bad type application, wrong branch type, or dialect-forbidden node;
- a mock generated evidence parameter passed through ordinary bindings and applications, without implementing an interface system;
- a mock fact that is established, preserved through one rewrite, consumed by a
  later rewrite, and erased before low-level lowering, including a stale-fact
  rejection case;
- a mock opaque or continuation-bearing boundary sufficient to test traversal and validation, without exposing it as surface Ash.

Compare direct interpreters on:

- whether evaluation order and continuations are observable in implementation data;
- whether host stack limits or exception behavior leak into language behavior;
- the amount of machinery required for the pure cases;
- whether both dialects can share machine components without erasing their invariants.

Compare rule organizations on:

- whether each semantic decision has one traceable caller path;
- whether diagnostics retain structured reasons;
- whether swapping a generalization or coverage policy affects only the rule boundary;
- whether normalization, equality, unification, and constraint resolution can be tested independently.

Retain a prototype only if it supplies current design evidence that cannot be captured more cheaply in examples, measurements, and counterexamples. No prototype should become production architecture without a later decision and task.

The retained [rank-1 integration report](mini-ash/rank-1-polymorphism/evidence.md)
records the implemented Mini-Ash result. Explicit type abstraction and
application made scheme scope, substitution, transformation, malformed-Core
rejection, and runtime erasure independently observable. Structured patterns
remain in the retained Core; decision Core and pattern compilation remain
excluded.

## Open questions

- Which exact type annotations belong on Core nodes, binders, patterns, and branches?
- Is explicit type abstraction/application sufficient for rank-1 Core, or are type schemes also stored at binding sites?
- How should elaboration record inserted operations without overwhelming source diagnostics?
- Do structured and decision patterns justify two dialects, two node families in one dialect, or one form plus ephemeral lowering data?
- Which invariants must `compile_patterns` establish beyond type preservation?
- Which representation changes qualify as retained semantic Core dialects subject to direct execution, and which are only lowering artifacts?
- Which transition and frame composition keeps the accepted explicit machine
  reviewable as the pure interpreter grows?
- What continuation representation remains inspectable without making ordinary pure terms awkward?
- Which semantic rules belong to Core validation, surface elaboration, or shared static infrastructure?
- How are proof obligations or established facts attached to transformed Core without trusting stale evidence?
- Which facts belong in types, explicit evidence terms, validated side tables, or
  analysis results, and what invalidates each representation?
- What minimal mock evidence test is useful without designing interfaces prematurely?
- How can an opaque CPS or other representation region expose a typed interface without pretending Core can inspect its contents?
- Which transformations are simpler before pattern lowering, and which after?
- When does a new Core dialect provide enough invariant value to justify conversion and validation costs?
- What observable behavior should differential execution compare before effects and richer runtime state exist?
