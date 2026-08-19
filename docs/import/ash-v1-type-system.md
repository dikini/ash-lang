# Ash V1 Type System — Initial Design Note

## Status

This note distills the current design direction for the first Ash type system and the architectural trajectory beyond it.

It is a design note, not a specification. It records the current intended shape of v1, the reasons for those choices, the implementation architecture they imply, and the seams deliberately preserved for later features.

The governing reboot principle is that Ash should begin as a small coherent language while future design prevents obvious architectural mistakes without becoming current language semantics. The first implementation is explicitly intended to test the parser, type system, and Core architecture while they remain cheap to change.

The type system therefore aims to be:

- small enough to implement and understand;
- expressive enough for the initial pure functional language;
- explicit about where inference stops;
- fully represented in typed Core;
- structurally ready for later effects, interfaces, rows, associated types, opacity, existentials, generative identity, and static propositions;
- free of speculative implementations of those later features.

The central design guide is:

> **Follow the types.**

Surface introduction, elimination, pattern structure, application, and elaboration should expose distinctions already present in the type structure rather than create parallel semantic concepts.

---

# 1. V1 scope

The initial Ash language is pure and functional. Its likely early nucleus consists of primitive values, immutable bindings, functions and calls, recursion, algebraic data types, pattern matching, and basic parametric polymorphism. Effects and the more ambitious static features are deliberately downstream.

The v1 type system is therefore:

> **A kinded, rank-1 parametric type system with explicit global interfaces, bidirectional local elaboration, conservative local generalization, nominal ADTs, structural tuples and records, type-directed patterns, and fully typed executable Core with explicit polymorphism.**

First-order unification supplies part of the inference mechanism, but Ash should not be defined conceptually as “an HM language”. Hindley–Milner techniques are useful inside the first implementation; they are not the intended ceiling of the language.

---

# 2. V1 and v1+ boundary

| V1 commitment | V1 implementation | V1+ trajectory, not implemented |
|---|---|---|
| Parametric polymorphism | kinded `forall`, explicit Core type abstraction/application | higher-rank and higher-kinded polymorphism |
| Functions | domain → codomain | computation/effect typing |
| Type application | unary and kind-directed | type lambdas and richer type expressions |
| ADTs | nominal types, ordinary polymorphic constructor values | opaque and existential abstraction |
| Tuples | structural positional products | specialized representation/layout |
| Records | closed labelled structural products | row polymorphism and richer equivalence |
| Globals | explicit signatures | global inference |
| Locals | bidirectional checking and first-order inference | richer constraint inference |
| Local polymorphism | conservative rank-1 generalization | effect/generativity-aware generalization |
| Recursion | monomorphic recursive inference | inferred polymorphic recursion |
| Patterns | typed structured matching | guards/refinement-dependent matching |
| Constraints | equality and kinds | interfaces, rows, propositions, associated-type equations |
| Core | fully typed and directly interpretable | effects, handlers, CPS |
| Core transforms | explicit representation/dialect contracts | representation-search optimization |

The purpose of the rightmost column is architectural pressure, not feature commitment.

---

# 3. Kinds

Kinds exist from the beginning because partially applied type constructors are genuine type expressions.

Conceptually:

```text
Kind :=
    Atom(KindId)
    Arrow(Kind, Kind)
```

V1 defines one atomic kind:

```text
Type
```

Examples:

```text
Int       : Type
List      : Type -> Type
Result    : Type -> Type -> Type
```

Kind application follows the ordinary rule:

```text
F : K1 -> K2
X : K1
----------------
F<X> : K2
```

Therefore:

```text
Result<Int> : Type -> Type
```

is not an incomplete or malformed type expression. It is a valid partially applied type constructor.

This distinction matters even if v1 surface syntax rarely needs to expose such expressions. It leaves a clean path toward richer type expressions, higher-kinded polymorphism, and future alternatives to ad-hoc type-hole syntax.

Kinds should also be architecturally open to future atomic categories. V1 must not assume throughout the compiler that `Type` is the only atomic kind that could ever exist. Future row systems may justify other kinds, but v1 does not define them.

---

# 4. Type algebra

The current semantic type algebra is:

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

Binder :=
    {
        variable,
        kind
    }
```

This is deliberately small.

It contains enough structure to express v1 cleanly while leaving later systems room to add new forms without changing the meaning of the existing ones.

## 4.1 Unary type application

Type application is semantically unary.

```text
Result<A, E>
```

means:

```text
Apply(
    Apply(Result, A),
    E
)
```

Surface syntax and compiler storage may flatten this for convenience, but kinding is defined as repeated unary application.

This means constructor “arity” is not a separate semantic validity rule. Kinding decides whether another argument may be applied.

That is important for partial type application and later higher-kinded type expressions.

---

# 5. Inference variables, rigid variables, and constructors

These are fundamentally different entities.

```text
?A : Type      inference variable
A! : Type      rigid variable
List           nominal type constructor
```

An inference variable may be solved:

```text
?A := Int
```

A rigid variable may not.

When checking:

```ash
id : A -> A
id(x) = x
```

the signature means conceptually:

```text
forall A : Type.
    A -> A
```

Inside the definition, `A` becomes rigid:

```text
A! -> A!
```

The body must work for whatever `A!` represents.

At a use site, however, polymorphism is instantiated with fresh inference variables:

```text
forall A. A -> A

    ↓ instantiate

?A -> ?A
```

Then:

```ash
id(42)
```

solves:

```text
?A := Int
```

This distinction is foundational and should be represented explicitly in compiler data.

---

# 6. Type identity and equality

Nominal type constructors are identified by declaration identity, not by spelling or representation.

Two declarations remain distinct even if structurally identical.

```ash
type UserId = ...
type OrderId = ...
```

introduce different nominal identities unless the language construct explicitly denotes a transparent alias.

This is compatible with the longer-term Ash direction in which identities may eventually bridge static and runtime worlds, while not implementing that stronger identity machinery in v1.

The compiler should keep three concepts distinct:

```text
type equality
type normalization / definitional equality
unifiability
```

They are simple enough to coincide frequently in v1, but later associated types, aliases, opacity, and richer type computation may cause them to diverge.

The authoritative semantics should therefore live in explicit rules rather than incidental comparison code.

---

# 7. Functions

Ash has one semantic notion of function.

The equational and operational surface styles are different presentations of the same typed function semantics and elaborate to the same Core.

The semantic form is:

```text
Function(domain, codomain)
```

These types are distinct:

```text
(A, B) -> C
```

and:

```text
A -> B -> C
```

because the latter means:

```text
A -> (B -> C)
```

## 7.1 Operational default

Operational multi-parameter syntax is naturally uncurried:

```ash
fn(x, y) {
    ...
}
```

corresponds to a product domain:

```text
(A, B) -> C
```

This matches programmer expectations and prevents partial application from appearing accidentally merely because a function has multiple parameters.

Nested arrow structure is introduced explicitly:

```ash
fn(x) {
    fn(y) {
        ...
    }
}
```

for:

```text
A -> B -> C
```

## 7.2 Equational form follows the declared type

Equational syntax is type-directed.

A declaration whose type contains successive arrows introduces successive function layers. A declaration whose domain is a tuple decomposes that tuple.

The grammar should therefore follow the typing structure rather than define an independent doctrine that “Ash functions are curried” or “Ash functions are n-ary”.

The design principle is stronger:

> **Arity and parameter grouping follow the function type.**

---

# 8. Quantification

Globals are always explicitly typed, as established by the function design. This creates stable module interfaces, supports separate checking, makes recursion predictable, and avoids global inference becoming part of the first reboot.

Free type variables in global signatures are implicitly universally quantified at the outermost boundary.

```ash
id : A -> A
```

means:

```text
forall A : Type.
    A -> A
```

and:

```ash
map : (A -> B, List<A>) -> List<B>
```

means:

```text
forall A : Type.
forall B : Type.
    (A -> B, List<A>) -> List<B>
```

Implicit quantification is outermost only.

It does not turn:

```text
(A -> A) -> Int
```

into:

```text
(forall A. A -> A) -> Int
```

Higher-rank polymorphism is outside v1.

Internally, every `forall` binder carries a kind even though the v1 quantification rule permits only binders of kind `Type`.

That restriction belongs to an explicit quantification rule, not to the representation.

---

# 9. Bidirectional local typing

Ash should use bidirectional elaboration.

The two central operations are conceptually:

```text
infer_expr(expr)
    -> TypedExpr, Type

check_expr(expr, expected_type)
    -> TypedExpr
```

Expected types flow inward whenever they are available.

The function design already explicitly expects this behavior for local functions.

Example:

```ash
let render : Item -> Text =
    fn(item) {
        item_to_text(item)
    }
```

The lambda is checked against:

```text
Item -> Text
```

so `item : Item` is known before checking its body.

Application follows the same principle:

```text
infer callee
instantiate outer polymorphism
expose its function type
check argument against its domain
produce the codomain
```

This avoids introducing unknowns unnecessarily and scales better than an “infer everything” architecture once types become richer.

---

# 10. Local generalization

V1 supports conservative rank-1 generalization at local bindings.

Obvious values generalize:

```ash
let id = fn(x) { x }
```

becomes:

```text
forall A.
    A -> A
```

so both:

```ash
id(1)
id("hello")
```

may be used independently.

But application-shaped expressions do not automatically generalize merely because the v1 language happens to be pure:

```ash
let x = make_something()
```

is initially treated more conservatively.

The purpose is trajectory.

Later, such an expression may perform effects, create generative identities, allocate resources, or return an existential package. A v1 rule that generalizes all pure applications would risk teaching programmers a behavior that later has to be revoked.

The policy should therefore be centralized:

```text
generalization_eligibility(
    expression,
    typing_facts
)
```

V1 may decide eligibility syntactically.

Later the same rule can consume:

```text
effect facts
generativity facts
resource information
existential escape information
```

if required.

The user-facing philosophy is:

> **Inference removes obvious repetition. It does not try to reconstruct hidden design intent.**

When inference becomes difficult, an annotation is acceptable and often improves the code by making an abstraction boundary explicit.

---

# 11. Recursive bindings

Initial `let rec` is restricted to functions, matching the current function design. General recursive values require separate decisions about initialization, cyclic data, and runtime failure.

Recursive uses are monomorphic during checking.

A provisional type may be assigned:

```text
visit : ?A -> ?B
```

and recursive calls are checked against that same provisional type.

The completed binding may later be generalized if eligible.

Polymorphic recursion is not inferred.

If a recursive definition genuinely requires distinct polymorphic instantiations, Ash should require an annotation rather than introducing significantly more complex inference.

---

# 12. Unification

V1 uses kind-preserving first-order structural unification.

It handles:

```text
inference variables
nominal constructors
type application
tuples
records
functions
```

Solving:

```text
?A := T
```

requires:

```text
kind(?A) = kind(T)
```

and an occurs check.

Thus:

```text
?A ~ ?A -> Int
```

is rejected.

Recursive ADTs are represented nominally through declarations; v1 does not infer arbitrary equi-recursive types.

Higher-kinded inference variables may be representable internally:

```text
?F : Type -> Type
```

but this does not imply higher-order unification.

The compiler need not infer from:

```text
?F<Int> ~ Result<Int, Error>
```

that:

```text
?F := λA. Result<A, Error>
```

Type-level lambda synthesis is outside v1.

---

# 13. Tuples and records

Tuples and records remain distinct semantic product forms.

They may share implementation utilities and may sometimes lower to identical physical layouts, but v1 does not claim that they are one semantic type constructor.

Starting distinct is conservative: unifying them later is substantially easier than discovering after broad compiler adoption that positional and labelled products require materially different equality, pattern, row, or optimization rules.

## 13.1 Tuples

Tuples are ordered structural positional products:

```text
(A, B)
```

Their order is semantic.

The likely initial treatment is:

```text
()       empty tuple / unit candidate
(A)      grouping
(A, B)   tuple
```

Unary tuples need not exist unless a real use case appears.

## 13.2 Records

Records are closed labelled structural products:

```text
{
    name : Text,
    age  : Nat
}
```

Fields use interned compiler labels:

```text
(LabelId, Type)
```

but ordinary labels are structural, not generative identities.

Two independent uses of `name` refer to the same structural label after ordinary name/qualification resolution.

The first implementation may preserve and compare field order. That is a v1 rule, not yet a permanent language commitment.

Ash should preserve the conceptual distinction between:

```text
source order
type equivalence order
physical layout order
```

even if v1 initially makes them coincide.

---

# 14. Record operations

Construction:

```ash
let user = {
    name = "Ada",
    age  = 42
}
```

infers:

```text
{name : Text, age : Nat}
```

Duplicate labels are rejected.

Projection:

```ash
user.name
```

uses a centralized field lookup rule.

Record patterns are label-directed:

```ash
let {name, age} = user
```

Partial decomposition is explicit:

```ash
{name, email, ..}
```

meaning that the named fields are required and bound while all remaining fields are intentionally ignored.

V1 records remain closed. `..` is an ignore-rest marker, not row polymorphism.

Functional update should initially modify existing fields only. Record extension and removal belong to future row design.

Named function arguments, if introduced, remain semantically distinct from record fields even if they share low-level symbol/label infrastructure.

---

# 15. ADTs and constructors

ADTs are nominal types, but their value constructors are ordinary polymorphic values.

For:

```ash
type Option<A> =
    None
    | Some(A)
```

the type constructor is:

```text
Option : Type -> Type
```

and the value constructors are:

```text
None :
    forall A.
    Option<A>

Some :
    forall A.
    A -> Option<A>
```

`Some(42)` therefore uses ordinary polymorphic instantiation and ordinary term application.

Constructors may also be passed as values:

```ash
map(Some, xs)
```

when ordinary typing permits it.

ADT-specific machinery belongs to metadata for:

```text
constructor identity
owner type
payload structure
pattern matching
coverage
visibility
runtime representation
```

not to ordinary application semantics.

---

# 16. Constructor payloads use ordinary products

Constructors do not introduce a third product mechanism.

A positional constructor:

```ash
Point(Float, Float)
```

has payload:

```text
(Float, Float)
```

and type:

```text
(Float, Float) -> Point
```

A labelled constructor:

```ash
User {
    name : Text,
    age : Nat
}
```

has payload:

```text
{name : Text, age : Nat}
```

and type:

```text
{name : Text, age : Nat} -> User
```

This gives an orthogonal model:

```text
nominality    supplied by the type/constructor declaration
product shape supplied by tuple or record
sum structure supplied by multiple constructors
```

The runtime remains free to flatten or specialize those products.

The semantic model does not require the runtime to allocate a record object inside a `User` object merely because the constructor payload is described as a record.

---

# 17. Structural and nominal products

Ash eventually needs both structural and nominal products.

Structural:

```text
(Int, Text)

{name : Text, age : Nat}
```

Nominal:

```ash
type Point =
    Point(Float, Float)

type User =
    User {
        name : Text,
        age : Nat
    }
```

The design separates two axes:

```text
identity:
    structural | nominal

shape:
    tuple | record
```

This avoids separate deep mechanisms for “nominal tuples” and “nominal records”.

A one-constructor ADT supplies nominality around an ordinary structural payload.

---

# 18. Type visibility and constructor visibility

Ash must support a type identity being visible without exposing how its values are constructed or deconstructed.

The eventual mechanism may involve modules, opaque types, existential packaging, generative identities, or combinations of them.

The capability is the commitment; the exact mechanism is deferred.

Therefore these decisions must not be fused:

```text
can name type
can construct value
can deconstruct / pattern-match value
```

A future module might expose:

```text
User : Type
```

and operations such as:

```text
create_user : {name : Text, age : Nat} -> User
name        : User -> Text
```

without exposing the `User` value constructor.

This is consistent with the longer-term existential direction, where relationships may be preserved through an unknown type identity without revealing what that identity is.

---

# 19. Pattern typing

Patterns are primarily checked against expected types:

```text
check_pattern(pattern, expected_type)
    -> PatternBindings
```

A tuple pattern follows tuple structure.

A record pattern follows labels.

A constructor pattern resolves constructor identity, instantiates its polymorphism, reconciles the constructor result with the expected nominal type, and checks the payload pattern against the resulting payload type.

Example:

```text
Some :
    forall A.
    A -> Option<A>
```

Checking:

```ash
Some(x)
```

against:

```text
Option<Int>
```

determines:

```text
x : Int
```

This is another application of “follow the types”: pattern structure is not inferred independently when the surrounding context already determines the type being decomposed.

---

# 20. Irrefutable `let` patterns

A `let` pattern must be statically established as irrefutable.

Tuple and closed-record destructuring are naturally irrefutable when their expected types match.

But:

```ash
let Some(x) = result
```

against:

```text
Option<A>
```

is refutable and is rejected in v1.

Ash should not silently insert runtime pattern failure here, just as the existing control-flow design avoids silently inserting failure or `Unit` for incomplete conditionals.

The rule should be semantic:

```text
pattern_irrefutability(pattern, expected_type)
```

rather than a syntactic ban on constructor patterns.

This leaves room for later refinement information to prove a constructor pattern irrefutable.

---

# 21. Exhaustiveness

Equational definitions and explicit `match` use the same pattern and coverage system. Equational functions elaborate to pattern matching rather than introducing a separate semantic mechanism.

V1 coverage should understand:

```text
closed ADTs
wildcards and binders
nested constructors
tuples
records where applicable
```

Recursive constructor coverage should be supported rather than limiting analysis to shallow top-level cases.

For example:

```ash
match x {
    None        => ...
    Some(True)  => ...
    Some(False) => ...
}
```

should be recognized as exhaustive when `Bool` is a closed two-constructor type.

Guards are deliberately excluded. The function design explicitly defers guards, contracts, refinements, value-dependent information, and proof/evidence terms as a related design cluster.

---

# 22. Explicit polymorphism in Core

Surface Ash may omit type abstraction and instantiation, but Core makes them explicit.

Surface:

```ash
id : A -> A
id(x) = x
```

elaborates conceptually to:

```text
ΛA : Type.
    fn(x : A) -> A {
        x
    }
```

and:

```ash
id(42)
```

becomes:

```text
(id [Int])(42)
```

Core therefore distinguishes:

```text
TermLambda
TermApply

TypeLambda
TypeApply
```

This explicitness is useful for specialization, monomorphization, later evidence passing, existential packaging, and Core transformations.

Surface omission is an elaboration convenience; Core retains the semantic operation.

---

# 23. Core patterns and decision forms

Core should be able to represent both structured patterns and compiled matching decisions.

Structured form:

```text
Match {
    scrutinee
    typed pattern cases
}
```

Compiled form:

```text
Case
constructor tests
projections
bindings
branches
```

Pattern compilation is therefore an explicit Core-to-Core transformation rather than an accidental side effect of parsing.

This allows useful transforms both before and after pattern lowering.

Before lowering, transforms may reason directly about:

```text
Some(x)
None
record decomposition
tuple decomposition
```

After lowering, transforms may reason about:

```text
constructor tests
branch sharing
field projections
dead branches
```

Ash should preserve semantic structure until a transform benefits from lowering it.

---

# 24. Core dialects

Different Core representations should have explicit admissible forms and invariants.

A plausible first division is:

```text
CoreStructured
CoreDecision
```

Both remain fully typed.

Transforms declare what they consume and produce:

```text
simplify_match :
    CoreStructured -> CoreStructured

compile_patterns :
    CoreStructured -> CoreDecision

simplify_case :
    CoreDecision -> CoreDecision
```

Dialect boundaries represent useful representation invariants, not mandatory chronological stages.

This matches the longer-term Core/CPS direction, in which different representations make different transformations natural and representation changes themselves may be compiler transformations.

The compiler should avoid proliferating micro-dialects. A dialect is justified only by materially different representation and useful invariants.

---

# 25. Direct Core execution

Every v1 Core dialect should be directly interpretable.

Direct interpretation is not merely a temporary bootstrap mechanism. It makes Core a semantic representation in its own right and supports differential testing of transforms:

```text
evaluate(program)
==
evaluate(transform(program))
```

for suitable test programs.

The interpreter should represent Ash evaluation state explicitly:

```text
Machine {
    control
    environment
    continuation
}
```

rather than using the host implementation language's call stack as the semantic representation of Ash continuations.

This is one deliberate place where the long-term effects design should influence v1 architecture.

The foundations already anticipate effects, handlers, explicit continuations, concurrency, cancellation, and runtime state and therefore identify small-step operational semantics as the stronger candidate for Ash's eventual normative semantics.

The effects exploration likewise makes continuation semantics part of the eventual language contract, distinguishing one-shot, multi-shot, abortive, and suspensive behavior.

V1 need not implement any of those distinctions. It should simply avoid hiding Ash control state in host recursion.

---

# 26. Explicit semantic rules

Ash compiler policy should be expressed through explicit authoritative semantic rules rather than interspersed checks.

Examples include:

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

Mechanism remains separate:

```text
union-find
substitution
type arenas
constraint storage
tree traversal
```

A semantic question should have one authoritative decision path.

Rules should return structured decisions rather than booleans where useful.

For example:

```text
GeneralizationDecision =
    Generalize(vars)
    | KeepMonomorphic(reason)
    | RequiresAnnotation(reason)
```

or:

```text
CoverageDecision =
    Exhaustive
    | MissingCases(patterns)
    | RequiresCatchall(reason)
```

This improves diagnostics and, more importantly, allows simple v1 policies to evolve without changing every caller.

For example:

```text
GeneralizationRule

v1:
    syntactic eligibility

later:
    syntax
    + effects
    + generativity
    + resource facts
```

The rest of the checker continues to ask the same semantic question.

---

# 27. Constraints and future evidence

V1 needs only a small constraint solver:

```text
type equality
kind equality
```

The architecture must nevertheless preserve a distinction among:

```text
unification
constraint resolution
type normalization
type equality
```

Future interfaces, rows, associated types, and propositions must not turn unification into one recursive “solve everything” procedure.

The long-term interface direction illustrates the distinction.

A future requirement:

```text
Eq<A>
```

is not itself evidence.

It says that evidence must exist.

Surface constrained polymorphism may eventually resemble:

```text
forall A.
    Eq<A> =>
    (A, A) -> Bool
```

and elaborate to explicit Core evidence passing, conceptually:

```text
ΛA.
λ(eqEvidence).
λ(args).
    ...
```

The physical implementation might later use dictionaries, specialization, monomorphization, or runtime indirection. The effects design already anticipates those alternatives for both interface and handler-related machinery.

None of this belongs in v1.

The v1 requirement is merely that compiler-generated typed evidence could later travel through ordinary Core bindings and applications without redefining function or polymorphism semantics.

---

# 28. Associated types and normalization trajectory

Associated types provide a useful pressure test because they introduce reducible type expressions whose meaning may depend on established evidence.

A future expression such as:

```text
Item<I>
```

may eventually normalize to:

```text
Text
```

when the relevant `Iterator<I>` implementation is known.

That reinforces the importance of keeping:

```text
normalization
equality
unification
constraint resolution
```

separate.

The current v1 type algebra does not need an associated-projection form. Adding one later should extend the type expression language rather than change the meaning of existing constructors, application, functions, or `forall`.

---

# 29. Effects trajectory

The effect system is a long-term goal, not a v1 feature.

The current effects direction expects structural effect rows such as:

```text
T ! { Database, Log | e }
```

to describe outstanding effect requirements, while handler composition remains ordered and semantically distinct from row composition.

V1 should therefore avoid several premature commitments.

## Do not bake purity permanently into `Function`

V1 functions are pure because v1 Ash is pure.

That does not mean:

```text
Function(domain, codomain)
```

must permanently encode intrinsic purity.

Later effect information might belong to arrows, computation types, or another representation. That remains open.

## Do not invent rows early

Record rows and effect rows may eventually share implementation machinery, but they are not assumed to be one semantic abstraction.

A shared algebra should be discovered, not presumed.

## Preserve the generalization seam

The conservative generalization rule can later consume effect and generativity facts without changing the semantics of `let`.

## Preserve kind extensibility

Future row systems may introduce new atomic kinds without requiring the kind checker to be redesigned.

These are architectural accommodations, not effect-system implementation.

---

# 30. Existentials and generative identity trajectory

The effects exploration anticipates packages of the conceptual form:

```text
exists α.
{
    identity : Identity<α>,
    provider : Provider<α>,
    handler  : Handler<α>
}
```

where the concrete identity `α` is unknown externally but relationships involving it remain statically preserved.

V1 does not implement existentials.

It does, however, already preserve several required distinctions:

```text
inference variables
rigid variables
nominal constructors
explicit scopes
explicit type binders
separate representation access
```

Later existential `pack`/`unpack` operations or stronger generative identities can therefore be added explicitly rather than reconstructed from a weaker type-variable model.

The important capability commitment remains:

> Ash must be able to expose and preserve type identity relationships without necessarily revealing concrete representation or construction authority.

---

# 31. V1 non-goals

The following are explicitly outside the initial type-system cut:

```text
global type inference
higher-rank polymorphism
user-visible higher-kinded polymorphism
higher-order unification
type-level lambdas
row polymorphism
effect typing
handlers
interfaces/typeclasses
associated types
constraint inference
opaque types
existential types
generative identities
refinement types
dependent typing
guards
contracts
propositions
laws
proofs
inferred polymorphic recursion
general recursive values
```

Some are expected Ash directions. Their exclusion means only that they are not prerequisites for the first coherent language.

This follows the reboot discipline that effects, providers, propositions, laws, proofs, and optimizer search should not be required for the first usable implementation.

---

# 32. Expected implementation responsibilities

The implementation will likely contain responsibilities roughly corresponding to:

```text
types
    Type
    Kind
    identities
    labels

type elaboration
    resolve constructors
    implicit outer quantification
    kind checking

inference
    fresh metavariables
    levels
    structural unification
    occurs checks

checking
    infer expression
    check expression
    instantiation
    function exposure

patterns
    pattern checking
    irrefutability
    coverage

generalization
    candidate discovery
    eligibility policy
    annotation requirement

declarations
    type constructors
    value constructors
    ADT metadata
    representation-access metadata

core
    fully typed terms
    explicit term/type abstraction and application
    structured matching
    decision matching
    dialect validation

interpreter
    explicit machine state
    explicit continuations

transforms
    typed Core -> typed Core
    explicit dialect contracts
```

These are conceptual boundaries, not yet mandatory source modules.

The same general architectural rule applies:

> **Mechanism should be reusable and boring; semantic policy should be explicit and testable.**

---

# 33. Initial evidence required

The first implementation should demonstrate not merely syntax acceptance but that the architectural choices work together.

Important cases include:

### Explicit global polymorphism

```ash
id : A -> A
id(x) = x
```

### Local polymorphic value

```ash
let id = fn(x) { x }

(id(1), id("hello"))
```

### Product-domain polymorphic function

```ash
map : (A -> B, List<A>) -> List<B>
```

with expected-type propagation into callbacks.

### Parameterized ADT

```ash
type Option<A> =
    None
    | Some(A)
```

with constructors behaving as ordinary polymorphic values.

### Exhaustive nested pattern matching

```ash
match value {
    None        => ...
    Some(True)  => ...
    Some(False) => ...
}
```

### Structural products

Tuple and record inference, construction, projection, and patterns.

### Partial record patterns

```ash
{name, email, ..}
```

### Nominal wrappers

Both tuple-shaped and record-shaped one-constructor ADTs.

### Visibility separation

Ability to represent a visible nominal type whose value constructor is not available in the current access context.

### Recursive typing

Ordinary monomorphic recursion succeeds; inferred polymorphic recursion does not.

### Kind checking

Partial type constructors are well-kinded; invalid kind application is rejected.

### Unification failures

Kind mismatches and occurs-check failures produce structured diagnostics.

### Surface equivalence

Equational and operational functions elaborate into equivalent typed semantics.

### Core execution

Structured Core executes directly.

### Core transformation

Pattern compilation produces decision Core.

### Decision Core execution

The transformed representation executes directly.

### Differential transform tests

Representative Core transforms preserve observable evaluation results.

These tests exercise the architecture, not merely individual syntax features.

---

# 34. Design rationale in one view

The main choices all follow a common pattern.

## Preserve distinctions when future equivalence is uncertain

Examples:

```text
tuple vs record
record rows vs effect rows
rigid variables vs inference variables
interface evidence vs effect handlers
type visibility vs constructor access
structured patterns vs decision trees
```

If later evidence shows two concepts are fundamentally one, unifying them is usually easier than recovering a distinction after it has leaked throughout the compiler.

## Make omission a surface convenience, not semantic absence

Surface Ash may omit:

```text
forall
type abstraction
type application
some local annotations
```

but Core makes required static structure explicit.

## Prefer annotations over heroic inference

Ash should infer what is locally determined and propagate expected types aggressively.

It need not infer hidden architectural intent.

Annotations at recursion boundaries, constrained abstractions, or difficult polymorphic points are acceptable and often improve readability.

## Keep future restrictions in rules, not representations

Examples:

```text
v1 only quantifies Type-kind variables
v1 only generalizes eligible local values
v1 uses order-sensitive record equality
v1 uses first-order unification
```

These are policies.

The representation should not make richer future behavior impossible.

## Keep Core semantic

Core is fully typed, directly executable, and capable of preserving useful high-level structure.

Lowering is an explicit transform, not the definition of meaning.

---

# 35. Resulting trajectory

The intended growth path is roughly:

```text
V1
    kinds
    primitive types
    functions
    tuples
    records
    nominal ADTs
    rank-1 parametric polymorphism
    local inference
    structured patterns
    executable typed Core

        ↓

V1+
    richer type expressions
    richer abstraction/visibility
    interfaces and explicit evidence
    associated type projections
    record rows
    effect rows
    effectful computation
    handlers
    opaque and existential packages
    generative identities

        ↓

Later
    richer constraints
    propositions
    laws
    proofs
    typed compiler facts
    more advanced optimization/search
```

The exact ordering beyond v1 remains open.

The important property is that the v1 nucleus does not need to be reinterpreted as those capabilities arrive.

---

# 36. Guiding test

The central test for the first-cut type system is:

> **Can Ash add its expected later typing capabilities by extending the type language, static facts, constraints, abstraction mechanisms, and Core forms without changing what existing v1 programs and v1 types mean?**

The current design appears to satisfy that test.

Effects do not require effect machinery in v1.

Interfaces do not require evidence machinery in v1.

Existentials do not require existential syntax in v1.

Rows do not require a generic row representation in v1.

But each has a clear place to enter later.

That is the intended balance:

> **Implement the smallest coherent type system now, while preserving the semantic seams required by the language Ash is intended to become.**