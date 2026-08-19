# DN-0006: Initial Type System

- ID: `DN-0006`
- Status: exploring
- Related: [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0002: Core Representation](DN-0002-core-representation.md), [DN-0005: Surface Function Definitions](DN-0005-surface-function-definitions.md), [DN-0007: Data and Pattern Typing](DN-0007-data-and-pattern-typing.md), [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md)

> This design note is informative and non-normative. It compares candidates for a first coherent type system; it does not define current Ash or commit later Ash to a trajectory. All syntax and internal forms are illustrative.

## Question

What is the smallest coherent account of kinds, type structure, functions, rank-1 polymorphism, local typing, recursion, and unification that can test Ash's surface and Core architecture without treating downstream capabilities as present requirements?

## Context and scope

[DN-0001](DN-0001-reboot-foundations.md) identifies a small pure functional nucleus as a likely starting point, but a design note does not make that nucleus current Ash. This note explores one type-system candidate for primitive types, immutable bindings, functions, calls, recursion, and parametric polymorphism. Data and pattern typing are separated into [DN-0007](DN-0007-data-and-pattern-typing.md); explicit typed Core is separated into [DN-0008](DN-0008-typed-core-and-elaboration.md).

The main candidate combines:

- kinded type expressions;
- rank-1 parametric polymorphism;
- explicit global interfaces;
- bidirectional local elaboration;
- conservative local generalization;
- monomorphic checking of recursive uses;
- kind-preserving first-order structural unification.

Calling this candidate “initial” describes the question being explored, not an accepted phase or release. Effects, interfaces, rows, associated types, opacity, existentials, generative identity, refinements, propositions, and higher-rank or higher-kinded polymorphism are architectural pressure only. This note neither requires them nor promises their order.

## Suggested design rules

### Represent kinds from the first coherent cut

> Suggested rule: Type constructors and type expressions carry kinds, with kind-directed unary application and at least one atomic kind such as `Type`.

A candidate kind algebra is:

```text
Kind :=
    Atom(KindId)
    Arrow(Kind, Kind)
```

Illustrative judgments include:

```text
Int       : Type
List      : Type -> Type
Result    : Type -> Type -> Type
Result<Int> : Type -> Type
```

Application follows the ordinary rule:

```text
F : K1 -> K2
X : K1
----------------
F<X> : K2
```

Semantically unary application lets `Result<A, E>` be surface sugar for `Apply(Apply(Result, A), E)`. Constructor arity need not become a separate validity rule when kinding already decides whether another argument is permitted.

The representation may allow future atomic kinds without inventing row or effect kinds now. Whether partially applied constructors need surface expression syntax in the first language remains open.

### Keep the initial type algebra small and explicit

> Suggested rule: Give inference variables, rigid variables, nominal constructors, application, products, functions, and universal quantification distinct semantic representations.

One candidate algebra is:

```text
Type :=
    InferVar(id, kind)
    RigidVar(id, kind)
    Constructor(id, kind)
    Apply(Type, Type)
    Tuple([Type])
    Record([(LabelId, Type)])
    Function(Type, Type)
    Forall(Binder, Type)

Binder := { variable, kind }
```

Tuples and records are included here only to show the boundary of the algebra; their equality, operations, and patterns are explored in [DN-0007](DN-0007-data-and-pattern-typing.md).

An inference variable can be solved, a rigid variable cannot, and a nominal constructor is identified by its declaration. Keeping those entities distinct avoids reconstructing scope and identity from names later.

### Separate equality, normalization, and unifiability

> Suggested rule: Type equality, type normalization or definitional equality, and unifiability are separate semantic questions even when an initial implementation often gives them the same answer.

Nominal constructors would compare by declaration identity, not spelling or representation. Thus two structurally identical nominal declarations remain different unless some separate construct is explicitly defined as a transparent alias.

The separation is pressure from possible aliases, opacity, associated projections, and type computation. None of those mechanisms needs to exist in the first coherent language. The immediate test is whether equality policy has one authoritative path instead of leaking into incidental host-language comparison code.

### Use one semantic function type

> Suggested rule: A function type is a domain and codomain, and surface parameter grouping follows that structure.

```text
Function(domain, codomain)
```

This keeps `(A, B) -> C` distinct from `A -> B -> C`, where the latter means `A -> (B -> C)`. An operational parameter list such as `fn(x, y) { ... }` can denote a product domain, while nested function expressions denote nested arrows. Equational presentation can follow the declared type rather than impose a separate arity doctrine. [DN-0005](DN-0005-surface-function-definitions.md) explores the surface consequences.

The representation should not settle where possible future computation or effect information belongs. Pure functions are enough to test this candidate; purity need not be baked into `Function` as a permanent promise.

### Quantify global interfaces at the outer boundary

> Suggested rule: A global interface is explicit, and its free type variables may be interpreted as outermost universal binders with explicit kinds internally.

For example:

```ash
id : A -> A
```

could mean:

```text
forall A : Type. A -> A
```

Likewise:

```ash
map : (A -> B, List<A>) -> List<B>
```

could quantify `A` and `B` at the global boundary. This does not place a `forall` beneath an arrow: `(A -> A) -> Int` would not silently become `(forall A. A -> A) -> Int`.

During definition checking, quantified variables become rigid. At a use site, outer polymorphism is instantiated with fresh inference variables. Explicit kinds on internal binders preserve the distinction between a representational capability and a candidate rule that initially permits quantification only over `Type`.

### Propagate expected types bidirectionally

> Suggested rule: Local elaboration has separate infer and check judgments, and expected types flow inward whenever available.

Conceptually:

```text
infer_expr(expr) -> TypedExpr, Type
check_expr(expr, expected_type) -> TypedExpr
```

For:

```ash
let render : Item -> Text = fn(item) {
    item_to_text(item)
}
```

the lambda can be checked against `Item -> Text`, making the parameter type available before checking the body.

Application can infer and instantiate the callee, expose a function type, check the argument against its domain, and return the codomain. This candidate aims to infer locally determined facts rather than reconstruct unstated abstraction intent.

### Generalize local bindings conservatively

> Suggested rule: The initial candidate generalizes an unannotated local binding at rank 1 only when its right-hand side is an anonymous function. Application-shaped right-hand sides remain monomorphic absent an annotation, and one centralized eligibility rule can later consume additional typing facts.

An anonymous-function right-hand side could generalize:

```ash
let id = fn(x) { x }

(id(1), id("hello"))
```

An application-shaped binding such as `let x = make_something()` remains monomorphic under this candidate unless an annotation requires polymorphism. That restriction does not follow from the candidate pure nucleus alone. Effects, generative identities, resources, or existential escape are possible pressures on a future eligibility rule, not features to implement now.

The policy should be centralized conceptually:

```text
generalization_eligibility(expression, typing_facts)
```

A later rule could consume more facts without making the initial representation pretend those facts already exist. Structured results such as `Generalize(vars)`, `KeepMonomorphic(reason)`, or `RequiresAnnotation(reason)` would support better diagnostics than a boolean.

### Check recursive uses monomorphically

> Suggested rule: A recursive binding is checked against one provisional monomorphic type; inferred polymorphic recursion is outside the initial candidate.

For a recursive function, checking may begin with a provisional shape such as `?A -> ?B`. Every recursive use sees that same provisional type. The completed binding could then be considered for ordinary local generalization.

Definitions requiring polymorphic recursion could require an annotation. General recursive values raise separate initialization and runtime questions; [DN-0005](DN-0005-surface-function-definitions.md) explores restricting the first surface form to function values.

### Limit unification deliberately

> Suggested rule: Inference uses kind-preserving first-order structural unification with an occurs check, while higher-order type synthesis remains outside the candidate.

The unifier can cover inference variables, nominal constructors, application, tuples, records, and functions. Solving `?A := T` requires matching kinds and rejects cycles such as:

```text
?A ~ ?A -> Int
```

Recursive ADTs can remain nominal rather than implying equi-recursive inference.

The representation might contain a higher-kinded inference variable such as `?F : Type -> Type` without solving:

```text
?F<Int> ~ Result<Int, Error>
```

by synthesizing a type-level lambda. Representability does not require higher-order unification.

## Candidate directions

### Kinded rank-1 system with first-order local inference

This is the main candidate above. It tests kinding, explicit interfaces, local polymorphism, and typed elaboration while giving annotations a deliberate role.

### Monomorphic first language

A monomorphic cut would reduce elaborator and Core complexity. It would also postpone testing whether rigid variables, instantiation, local generalization, and explicit Core polymorphism compose with functions and data. If those seams are central risks, postponement may produce less evidence than the smaller implementation cost warrants.

### HM-style inference with broad generalization

Inferring most rank-1 types and generalizing every eligible pure binding would be familiar and concise. It risks turning the candidate pure nucleus into a user-visible generalization promise and making future restrictions disruptive. It may also pull global inference into the language before stable module boundaries are understood.

### Annotation-led bidirectional system without local generalization

This direction preserves expected-type propagation but keeps local polymorphism explicit. It is easier to specify and may produce clearer boundaries, at the cost of repetition in common local helpers. Experiments should measure whether annotations are occasional guidance or pervasive noise.

### Delay kinds until higher-kinded features

An arity-based first implementation would be smaller on paper. It would classify partial application as malformed and could spread constructor-arity assumptions through representations and checking. A prototype should determine whether carrying kinds now is actually costly enough to justify that debt.

### Equality by normalized structure

Structural or normalized equality may be appropriate for transparent type forms, but using it for nominal constructors would erase declaration identity. A mixed system needs explicit rules for which forms are transparent, nominal, or reducible rather than one universal host comparison.

## Interactions and architectural pressure

- [DN-0005](DN-0005-surface-function-definitions.md) depends on the distinction between explicit global interfaces, locally inferred terms, tuple domains, nested arrows, and expected-type propagation.
- [DN-0007](DN-0007-data-and-pattern-typing.md) supplies product, ADT, pattern, and coverage cases that stress kinding, instantiation, equality, and unification.
- [DN-0008](DN-0008-typed-core-and-elaboration.md) explores whether omitted surface quantification and instantiation should become explicit Core operations and whether every transform can revalidate types.
- [DN-0002](DN-0002-core-representation.md) applies pressure for a typed Core whose function and continuation representation can grow beyond the initial pure language. It does not require effects now.
- Possible interfaces distinguish a constraint requiring evidence from the evidence term itself. They pressure the design to separate unification, constraint resolution, normalization, and equality.
- Possible associated types pressure normalization and equality to remain separate from unification. No projection form is required in the initial algebra.
- Possible record and effect rows pressure kind representation and generalization seams, but do not establish one shared row algebra.
- Possible opacity, existentials, and generative identity pressure rigid variables, nominal identity, binder scope, and representation access to remain distinct. They are not initial requirements.
- Possible effects pressure generalization policy and function typing without deciding whether effect information belongs on arrows, computations, or another form.

## Evidence and experiments

A type-checker and elaborator prototype should be limited to the positive cases, negative cases, and comparison observations listed below, using provisional syntax. Retain its code only if a later task authorizes it; otherwise preserve measurements and counterexamples as design evidence.

Positive cases should include:

- an explicitly typed polymorphic global such as `id : A -> A`;
- a locally generalized function used at two unrelated types;
- a product-domain polymorphic function with an expected-typed callback;
- partial application of a multi-parameter type constructor with valid kinds;
- ordinary monomorphic recursive inference;
- paired equational and operational functions with the same inferred body facts.

Negative cases should include:

- a rigid variable incorrectly unified with a concrete type while checking a global;
- a kind mismatch in type application;
- an occurs-check failure;
- a higher-order unification problem the candidate intentionally refuses;
- inferred polymorphic recursion;
- a local application whose generalization status is ambiguous;
- an omitted annotation at a boundary the candidate cannot infer predictably.

Record for each candidate:

- the annotations required in representative small programs;
- where fresh inference variables are introduced and solved;
- whether kind and scope errors yield structured diagnostics;
- whether equality, normalization, unification, and constraint resolution have separate call paths;
- whether all inferred surface omissions become explicit, checkable Core structure;
- whether adding a mock future fact to the generalization decision changes one rule or many callers.

## Open questions

- Is rank-1 polymorphism part of the smallest useful architectural test, or should a monomorphic cut come first?
- Should global free type variables be implicitly quantified, explicitly bound, or support both presentations?
- Does the first surface language expose partially applied type constructors, or only represent them internally?
- Which atomic kinds, if any beyond `Type`, are justified by present evidence?
- How are transparent aliases, if any, distinguished from nominal declarations?
- What is the initial equality rule for records, including field order?
- Which value forms beyond anonymous-function right-hand sides, if any, should become eligible for generalization?
- When should a local annotation be required instead of introducing more inference variables?
- How are mutually recursive bindings checked and generalized?
- Which annotations, if any, permit polymorphic recursion?
- Does function exposure instantiate only outer polymorphism, and how is failure reported?
- Where do type levels, substitutions, union-find state, and scoped rigid variables live without turning mechanisms into semantic policy?
- Which future pressure is sufficiently concrete to test now, and which should remain only a named seam?
