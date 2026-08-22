# DN-0007: Data and Pattern Typing

- ID: `DN-0007`
- Status: exploring
- Related: [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0002: Core Representation](DN-0002-core-representation.md), [DN-0005: Surface Function Definitions](DN-0005-surface-function-definitions.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md)

> This design note is informative and non-normative. It explores data and pattern-typing candidates; it does not define current Ash, accept syntax, or commit future abstraction or row features. All syntax is illustrative.

## Question

Can tuples, records, and algebraic data types share a small set of product, nominality, and pattern-typing mechanisms while preserving the distinctions needed for visibility, irrefutable binding, and useful coverage analysis?

## Context and scope

The candidate type algebra in [DN-0006](DN-0006-initial-type-system.md) distinguishes tuple and record products from nominal type constructors. This note investigates the semantic consequences of that split:

- structural positional tuples and structural labelled records;
- nominal algebraic data types and ordinary constructor values;
- tuple-shaped and record-shaped constructor payloads;
- separate visibility for type identities and value constructors;
- type-directed pattern checking;
- irrefutability of binding patterns;
- shared coverage analysis for matches and function equations.

The goal is to find a coherent initial model, not to define current Ash. Row polymorphism, named arguments, opaque modules, existential packages, generative identity, refinements, guards, contracts, and representation layout are downstream pressure or separate design questions.

## Suggested design rules

### Keep tuples and records semantically distinct

> Suggested rule: Tuples are ordered structural positional products, while records are closed structural labelled products.

Illustrative tuple shapes are:

```text
()       empty tuple or unit candidate
(A)      grouping candidate
(A, B)   ordered tuple
```

A unary tuple need not exist without a concrete use. Tuple order is semantic.

An illustrative record type is:

```text
{
    name : Text,
    age  : Nat
}
```

Compiler labels may be interned, but an ordinary label remains structural rather than a fresh identity. Independent resolved uses of `name` would refer to the same label.

The design should distinguish source field order, type-equivalence order, and physical layout order even if an initial candidate temporarily makes them coincide. Keeping tuples and records distinct is conservative: later evidence can unify mechanisms more easily than it can recover semantic distinctions after they spread through equality, patterns, rows, and transforms.

### Keep record operations closed and label-directed initially

> Suggested rule: Record construction rejects duplicate labels, projection uses one field-lookup rule, patterns select fields by label, and any initial update operation changes existing fields only.

```ash
let user = {
    name = "Ada",
    age  = 42
}

user.name
```

A closed-record pattern may bind every field:

```ash
let {name, age} = user
```

An explicit ignore-rest marker is one candidate for partial decomposition:

```ash
match user {
    {name, ..} => use(name)
}
```

Here `..` would ignore known remaining fields. It would not introduce an open row or infer record extension. Record extension and removal should wait for evidence from row design rather than emerge accidentally through update syntax.

Named function arguments, if explored, may reuse label infrastructure but would remain semantically distinct from record fields until a design establishes otherwise.

### Treat ADTs as nominal types with ordinary constructor values

> Suggested rule: An algebraic data declaration introduces a nominal type identity, while each value constructor has an ordinary polymorphic value type.

For illustrative syntax:

```ash
type Option<A> =
    None
    | Some(A)
```

the type constructor and value constructors could have:

```text
Option : Type -> Type

None : forall A. Option<A>
Some : forall A. A -> Option<A>
```

`Some(42)` would use ordinary instantiation and application, and `Some` could be passed as a value when ordinary typing permits it.

ADT-specific metadata would still record constructor identity, owner type, payload structure, visibility, coverage membership, and runtime representation. That metadata need not create a second application semantics.

### Build constructor payloads from ordinary products

> Suggested rule: Constructor payload shape comes from tuple or record products; the enclosing declaration supplies nominal identity and multiple constructors supply sum structure.

A positional constructor such as:

```ash
Point(Float, Float)
```

could have a tuple payload and type:

```text
(Float, Float) -> Point
```

A labelled constructor such as:

```ash
User {
    name : Text,
    age  : Nat
}
```

could have a record payload and type:

```text
{name : Text, age : Nat} -> User
```

This separates two axes:

```text
identity: structural | nominal
shape:    tuple | record
```

A one-constructor ADT can therefore wrap an ordinary product to create a nominal product. The semantic payload model does not require the runtime to allocate a nested tuple or record object; representation and layout remain independent.

### Separate type visibility from construction and deconstruction access

> Suggested rule: The ability to name a nominal type, construct its values, and deconstruct or pattern-match its values are separate access decisions.

A future abstraction boundary might expose:

```text
User : Type
create_user : {name : Text, age : Nat} -> User
name : User -> Text
```

without exposing a `User` constructor. The initial representation should be able to describe that access distinction even if the surface module, opacity, or packaging mechanism is not yet chosen.

This is a capability pressure, not a commitment to modules, opaque types, existentials, or generative identities in the first coherent language.

### Check patterns against expected types

> Suggested rule: Pattern typing primarily checks a pattern against an expected type and returns the bindings introduced by that pattern.

Conceptually:

```text
check_pattern(pattern, expected_type) -> PatternBindings
```

A tuple pattern follows the expected tuple structure. A record pattern resolves labels against the expected record. A constructor pattern resolves constructor identity, instantiates its polymorphism, reconciles the constructor result with the expected nominal type, and checks its payload.

For example, checking `Some(x)` against `Option<Int>` would instantiate the constructor and determine `x : Int`. Pattern structure would not be inferred independently when the surrounding scrutinee already determines what is being decomposed.

### Require binding patterns to be irrefutable

> Suggested rule: A pattern in an unconditional `let` binding is accepted only when its success is statically established for the expected type.

Tuple and complete closed-record destructuring are natural irrefutable candidates when their expected types match. A constructor pattern such as:

```ash
let Some(x) = result
```

is refutable for `Option<A>` and would be rejected under this rule rather than silently inserting runtime pattern failure.

The check should be semantic:

```text
pattern_irrefutability(pattern, expected_type)
```

rather than a blanket syntactic ban on constructor patterns. This leaves a seam for possible future static facts that prove a pattern irrefutable without requiring those facts now.

### Share one coverage system across matches and equations

> Suggested rule: Explicit matches and equational function definitions use the same typed pattern representation and coverage analysis.

The coverage candidate should understand closed ADTs, wildcards and binders, nested constructors, tuples, and relevant record decomposition. It should reason recursively enough to recognize cases such as:

```ash
match value {
    None        => ...
    Some(True)  => ...
    Some(False) => ...
}
```

as exhaustive when both `Option` and `Bool` have the assumed closed constructor sets.

One surface policy could require every conditional to define a result for every input, reject `if` without `else`, and require a catchall unless typed coverage proves completeness. That is a candidate policy, not a current Ash rule.

Guards are excluded from the initial coverage candidate. A conservative later rule could refuse to count guarded clauses toward guaranteed coverage, but guard-aware coverage should be designed with guards, refinements, contracts, and value-dependent evidence rather than assumed here.

## Candidate directions

### Distinct structural tuple and record forms

This is the main candidate. It makes positional order and labels explicit and lets later row evidence determine whether record equality or decomposition should change.

### One generalized product form

A single labelled-or-positional product representation may reduce compiler cases. It risks making tuple order, record equality, partial patterns, named arguments, and future row operations appear equivalent before evidence supports that claim.

### Nominal records and tuples as separate primitive families

Dedicated nominal-record and nominal-tuple mechanisms could offer direct syntax and access control. They duplicate product typing, pattern, and representation machinery that a one-constructor ADT might supply orthogonally.

### Constructors as special application forms

Special constructor-call typing can expose targeted diagnostics and representation facts directly. Treating constructors as ordinary polymorphic values instead reuses instantiation and application, supports higher-order use, and confines ADT-specific work to identity, payload, patterns, coverage, visibility, and layout metadata.

### Order-sensitive or order-insensitive record equality

Preserving and comparing source order is a smaller first implementation. Canonicalizing labels gives the usual structural intuition that field order is irrelevant but requires a policy for diagnostics, duplicate detection, layout, and source reconstruction. The representation should not conflate this choice with physical order.

### Shallow or recursive coverage analysis

Top-level constructor checking is simpler but rejects or requires catchalls for visibly complete nested matches. Recursive constructor-space analysis is more useful, though it must control complexity and produce understandable missing-case diagnostics.

### Runtime failure for refutable bindings

Allowing `let Some(x) = result` would be concise but introduces implicit failure semantics and makes binding behavior depend on runtime matching. Requiring explicit `match` keeps failure and alternatives visible. A future refinement-aware rule could revisit particular cases.

## Interactions and architectural pressure

- [DN-0006](DN-0006-initial-type-system.md) supplies kinds, instantiation, nominal identity, products, equality, and expected-type checking. Record field order is an open equality question shared by both notes.
- [DN-0005](DN-0005-surface-function-definitions.md) relies on the same pattern typing and coverage for equation heads and explicit matches. Anonymous equation syntax must remain distinct from binding destructuring.
- [DN-0008](DN-0008-typed-core-and-elaboration.md) explores retaining structured typed patterns before compiling them into decision forms. Coverage and irrefutability should not become accidental parser or lowering behavior.
- [DN-0002](DN-0002-core-representation.md) uses ADTs and matching as representation experiments. Data semantics should remain independent of any chosen runtime layout.
- Possible record rows pressure field equality, partial patterns, extension, and kinding. They do not show that record rows and effect rows share one semantic algebra.
- Possible opacity, existentials, and generative identities pressure the separation among type identity, representation, construction authority, and deconstruction authority. They do not require those features now.
- Whether and how later refinement or proposition facts become inputs to irrefutability and coverage remains an open interface question. The initial APIs do not assume such facts or invent a refinement system.

- Pattern coverage affects diagnostics, formatter behavior, generated code, and teaching. A syntactically concise rule that produces opaque missing-case reports may not be the best candidate.

## Evidence and experiments

A data-and-pattern prototype should be limited to the cases and comparison observations listed below and should compare semantic candidates independently of final syntax or runtime layout. Prototype code is disposable unless later retained through an authorized task.

Positive cases should cover:

- tuple and record construction, checking, projection, and destructuring;
- duplicate-label rejection and missing-field diagnostics;
- an explicit ignore-rest record pattern over a closed record;
- parameterized ADTs whose constructors instantiate as ordinary values;
- passing a constructor as a higher-order value;
- tuple-shaped and record-shaped one-constructor nominal wrappers;
- a visible nominal type with unavailable construction and deconstruction capabilities;
- irrefutable tuple and record `let` patterns;
- exhaustive top-level and nested constructor matches;
- equivalent coverage behavior for equations and explicit matches.

Negative cases should cover:

- equating distinct nominal declarations with identical payloads;
- using a constructor from the wrong owner type;
- projecting an absent field;
- duplicate record fields;
- treating `..` as an inferred open row;
- a refutable constructor pattern in an unconditional binding;
- non-exhaustive nested matches and unreachable clauses;
- construction or deconstruction without the relevant access capability.

Compare candidates on:

- whether one pattern checker handles tuples, records, and constructor payloads without losing form-specific diagnostics;
- whether coverage reports useful missing patterns and scales to nested closed types;
- whether source order, equality order, and layout order remain independently changeable;
- whether constructors really use ordinary instantiation and application outside patterns;
- whether access checks can distinguish naming a type from constructing or deconstructing it;
- whether structured patterns can be preserved and later compiled without changing evaluation.

## Open questions

- Are tuples and records both needed in the first coherent language, or can one wait without hiding architectural risk?
- Is `()` a tuple, a distinguished unit value, or both by definition?
- Should unary tuples exist?
- Is record type equality initially sensitive to field order?
- What syntax makes ignore-rest distinct from row extension, spread, and update?
- Should record update exist initially, and if so, how does it prove that a field already exists?
- Are named arguments independent from records at both surface and semantic levels?
- Which constructor payload syntax maps most clearly to tuple and record products?
- What declaration metadata is required to resolve constructor ownership and visibility?
- Which abstraction mechanism will eventually express separate construction and deconstruction access?
- How should pattern typing report ambiguity when constructors share unqualified names?
- How deep should initial coverage analysis recurse, and how should it bound complexity?
- Should unreachable or redundant cases be errors, warnings, or tooling feedback?
- Are wildcard and `else` distinct catchall forms, and do they carry different binding or diagnostic behavior?
- What static facts, if any, can make a constructor pattern irrefutable without introducing hidden runtime failure?

## Retained implementation evidence

The accepted monomorphic subset now has a retained
[data-and-pattern integration report](mini-ash/data-and-patterns/evidence.md).
The report confirms transfer for structural tuples, nominal identity, ordinary
constructor values, expected-type patterns, semantic irrefutability, and shared
recursive coverage. It does not transfer this note's polymorphism, records,
rows, access control, or abstraction candidates into current Ash.
