# Ash Kind Declarations and Type Promotion — Initial Design Note

## Status and intent

This note explores user-defined kind declarations and restricted type promotion as possible future Ash features.

The immediate motivation is developer experience for state-indexed APIs, typestate, session types, protocol states, multiplicities, continuation modes, and similar finite static domains.

The current Ash type-system direction already represents kinds explicitly and deliberately avoids assuming that `Type` must remain the only atomic kind forever.

The current hypothesis is:

> **Ash may benefit from a small `kind` declaration for finite static domains, with optional promotion from compatible `type` declarations into the same static representation.**

The goal is not to introduce general dependent typing or unrestricted term-to-type promotion.

The feature should remain small enough that most of its cost lies in declaration elaboration, surface grammar, namespaces, and diagnostics rather than new type-checking theory.

---

# 1. Motivation

State-indexed APIs are easier to understand when protocol states have direct static names.

For example, a transaction protocol should ideally be able to expose types such as:

```text
Session<Transaction, Idle>
Session<Transaction, Open>
Session<Transaction, Closed>
```

and transitions such as:

```text
begin :
    Session<Transaction, Idle>
    -> Session<Transaction, Open>

query :
    Session<Transaction, Open>
    -> Session<Transaction, Open>

commit :
    Session<Transaction, Open>
    -> Session<Transaction, Closed>
```

This can technically be encoded by declaring `Idle`, `Open`, and `Closed` as ordinary nominal types.

That representation is likely sufficient for expressivity, but it is poor developer experience because protocol states are not naturally understood as unrelated runtime types.

The desired model is instead:

```ash
kind TxState =
    Idle
    | Open
    | Closed
```

where:

```text
Idle   : TxState
Open   : TxState
Closed : TxState
```

are static inhabitants of the newly introduced kind.

This makes the protocol structure visible directly in the type language.

---

# 2. Existing architectural seam

The current kind representation is:

```text
Kind :=
    Atom(KindId)
    | Arrow(Kind, Kind)
```

V1 introduces only the atomic kind:

```text
Type
```

but the architecture explicitly leaves room for future atomic kinds.

A user-defined kind therefore fits the existing model naturally.

A declaration such as:

```ash
kind TxState =
    Idle
    | Open
    | Closed
```

would conceptually allocate:

```text
Atom(TxStateId)
```

and introduce static constructors whose kind is that atom.

No new kind algebra is required for the basic case.

---

# 3. Do not require a kind-of-kinds

The declaration:

```ash
kind TxState =
    Idle
    | Open
    | Closed
```

introduces the atomic kind `TxState`.

The design should not initially require a judgment such as:

```text
TxState : Kind
```

because Ash has not established `Kind` as a first-class kind-of-kinds in the language.

It is sufficient to say:

```text
TxState
    is an atomic kind

Idle   : TxState
Open   : TxState
Closed : TxState
```

This keeps the feature within the current kind representation rather than introducing another universe level merely for notation.

---

# 4. Basic introduction rule

The first form can be deliberately narrow:

```text
kind K =
    C1
    | C2
    | ...
    | Cn
```

Conceptually, the declaration requires:

```text
K is a fresh nominal kind identity

each Ci is a fresh constructor identity
within the relevant namespace

each Ci is nullary

n >= 1
```

and introduces:

```text
Atom(K)

C1 : K
C2 : K
...
Cn : K
```

The kind itself is nominal.

Two independently declared kinds are distinct even if they contain corresponding constructors.

For example:

```ash
kind FileState =
    Open
    | Closed

kind SocketState =
    Open
    | Closed
```

introduce distinct static domains:

```text
FileState != SocketState
```

The treatment of the repeated source names `Open` and `Closed` depends on namespace and qualification rules and remains a surface-design question.

---

# 5. Initial admissible declaration shape

The smallest useful form is:

> **A finite non-empty nominal sum of nullary static constructors.**

Valid:

```ash
kind State =
    Idle
    | Open
    | Closed
```

Valid:

```ash
kind Multiplicity =
    Linear
    | Affine
    | Unrestricted
```

Valid:

```ash
kind ContinuationMode =
    OneShot
    | MultiShot
    | Abortive
    | Suspensive
```

Valid:

```ash
kind Ownership =
    Exclusive
```

The singleton case is harmless and may be useful.

An empty kind should not be introduced initially unless a concrete use case demonstrates a need for it.

---

# 6. Forms initially excluded

The initial declaration should not support constructor payloads:

```ash
kind Maybe =
    None
    | Some(Type)
```

It should not initially support parameters:

```ash
kind Maybe<A> =
    None
    | Some(A)
```

It should not initially support recursive static data:

```ash
kind Nat =
    Zero
    | Succ(Nat)
```

It should not support arbitrary static expressions in alternatives.

These forms introduce additional questions involving:

```text
parameterized kinds
higher-kinded static constructors
recursive normalization
static constructor application
type-level recursion
kind polymorphism
type-level pattern matching
```

They should be introduced only in response to concrete pressure.

---

# 7. Static constructors are type-level terms

A constructor introduced by a `kind` declaration participates in the static/type language.

For example:

```ash
kind TxState =
    Idle
    | Open
    | Closed
```

allows:

```text
Session<Transaction, Open>
```

provided that the corresponding parameter expects an inhabitant of `TxState`.

The constructor `Open` is not necessarily a runtime value.

There need not initially be an expression:

```ash
let x = Open
```

corresponding to that static constructor.

This distinction is important.

A `kind` declaration introduces a static domain directly rather than manufacturing runtime values solely so that they can later be lifted into the type language.

---

# 8. Variables may range over user-defined kinds

Rigid variables and inference variables should be able to carry a user-defined kind.

For example:

```text
S! : TxState
?S : TxState
```

The existing distinction between inference variables and rigid variables remains unchanged.

Ordinary kind-preserving solving then gives:

```text
?S := Open
```

as valid, while:

```text
?S := Int
```

is invalid because:

```text
Open : TxState
Int  : Type
```

The current unifier already requires inference-variable solutions to preserve kind.

The basic feature therefore does not require new unification theory.

---

# 9. Type constructors may accept user-defined-kind parameters

The important use case is not merely naming static constructors.

Types must be able to be indexed by them.

Conceptually:

```text
Session :
    Protocol
    -> TxState
    -> Type
```

or, for a resource:

```text
Resource :
    ResourceKind
    -> State
    -> Multiplicity
    -> Type
```

Then:

```text
Session<Transaction, Open>
Resource<File, Open, Linear>
```

are ordinary well-kinded type applications.

The existing kind application rule remains sufficient:

```text
F : K1 -> K2
X : K1
----------------
F<X> : K2
```

No special rule for protocol states is required.

---

# 10. User-defined kinds do not imply kind polymorphism

Allowing:

```text
S : TxState
```

does not imply support for abstraction over arbitrary kinds.

Ash may support:

```text
forall S : TxState.
    ...
```

without supporting:

```text
forall K.
    ...
```

or:

```text
forall K.
forall X : K.
    ...
```

These are materially different capabilities.

User-defined kinds provide additional static domains.

Kind polymorphism allows abstraction over those domains.

The latter should remain a separate design question.

---

# 11. Quantification policy must evolve explicitly

The current v1 representation already stores a kind on every `forall` binder, but v1 policy restricts quantified variables to kind `Type`.

User-defined kinds would require relaxing that policy when a declaration needs to quantify over one.

For example:

```text
forall S : TxState.
    Session<P, S> -> ...
```

The representation does not need to change.

The quantification rule does.

This fits the existing architectural principle that future restrictions should live in semantic rules rather than representations.

---

# 12. Direct kind declarations should be the semantic foundation

A direct declaration:

```ash
kind TxState =
    Idle
    | Open
    | Closed
```

should be sufficient to express the static domain.

No promotion feature is required for the semantics.

This gives an important design principle:

> **`kind` is semantic; promotion is elaboration.**

If promotion is introduced, it should derive the same static objects that could have been introduced directly by an admissible `kind` declaration.

Promotion should not expand what the static type language can express.

---

# 13. Restricted type promotion

Consider:

```ash
type TxState =
    Idle
    | Open
    | Closed
```

A programmer may want the same conceptual alternatives both at runtime and as static indices.

A promotion declaration could request this explicitly:

```ash
promote TxState
```

Conceptually, promotion derives a corresponding static domain:

```text
promoted kind TxState

Idle   : promoted TxState
Open   : promoted TxState
Closed : promoted TxState
```

The actual namespace and source spelling of the promoted kind remains open.

The central point is semantic:

> Promotion derives a kind declaration from a compatible type declaration.

---

# 14. Promotion admissibility

The first promotion rule should be intentionally conservative.

A type is promotable when its declaration has exactly a shape accepted by the current `kind` declaration rules.

Initially:

```text
Promotable(T)
iff
T is a finite non-empty nominal sum
whose constructors are all nullary
```

Thus:

```ash
type TxState =
    Idle
    | Open
    | Closed

promote TxState
```

is valid.

But:

```ash
type Option<A> =
    None
    | Some(A)

promote Option
```

is not initially valid.

Likewise:

```ash
type Nat =
    Zero
    | Succ(Nat)

promote Nat
```

is not initially valid.

This gives the invariant:

> **Anything produced through promotion could have been declared directly as a valid `kind`.**

That keeps promotion purely ergonomic.

---

# 15. Promotion should not imply general DataKinds-style lifting

The initial promotion feature should not mean:

```text
every type becomes a kind

every value constructor becomes a static constructor

every constructor payload is promoted

every recursive datatype becomes recursive static data

every runtime value has a type-level representation
```

Those are much larger commitments.

The feature should instead mean only:

```text
a compatible nominal finite enumeration
may optionally acquire a corresponding static domain
```

This provides the desired protocol-state syntax without introducing a general dependent static language.

---

# 16. Runtime and static identity remain distinct

Promotion does not necessarily mean that the runtime constructor and static constructor are semantically the same entity.

For:

```ash
type TxState =
    Idle
    | Open
    | Closed

promote TxState
```

there may conceptually be:

```text
runtime Open
static  Open
```

with an explicit relation established by promotion.

Whether these share a compiler identity or have linked but separate identities should be determined by the requirements of reflection, diagnostics, namespaces, and future static/runtime bridging.

The initial feature need only establish that promotion associates corresponding alternatives.

It need not provide runtime reflection or reification.

---

# 17. Surface names and namespaces are a major design question

The aesthetically simplest promoted syntax is:

```ash
type TxState =
    Idle
    | Open
    | Closed

promote TxState

session : Session<Transaction, Open>
```

Here `Open` may refer to:

```text
Open : TxState            -- term-level constructor

Open : promoted TxState   -- static constructor
```

The compiler can potentially disambiguate these because term and static/type positions are already semantically distinct.

This would follow the general Ash principle of letting the expected type structure guide interpretation.

However, contextual resolution of identically spelled constructors is a user-facing design choice and should not be adopted accidentally.

Alternatives include qualified forms such as:

```text
TxState.Open
```

or explicit promotion syntax such as:

```text
#Open
```

The surface grammar should be explored independently of the core semantic model.

---

# 18. Type and kind declaration namespaces

A related question is whether this should be legal:

```ash
type State = ...
kind State = ...
```

Even if the compiler can distinguish type and kind namespaces, allowing unrelated declarations with the same source name may be confusing.

A conservative initial rule would make nominal `type` and `kind` declarations collide at the declaration level.

Promotion is different because the relationship is intentional.

A promoted type may reasonably share source spelling with its derived kind-level representation.

This distinction should be made explicit in the name-resolution design.

---

# 19. Exhaustiveness and equality are simple for the initial form

A finite static kind gives the compiler complete knowledge of its inhabitants:

```ash
kind State =
    Idle
    | Open
    | Closed
```

Static equality is nominal constructor identity:

```text
Idle == Idle
Idle != Open
```

No type-level reduction is required.

If future static pattern matching or exhaustive reasoning over kinds is introduced, the finite closed declaration provides natural coverage information.

That functionality is not required by the initial feature.

---

# 20. No dependent elimination is implied

Knowing:

```text
S : State
```

does not initially imply that Ash can inspect `S` at the type level and compute arbitrary resulting types.

The feature need not introduce:

```text
match S {
    Open   => ...
    Closed => ...
}
```

inside the static language.

Transitions may instead be expressed using interfaces, associated types, or explicit type-level relations already expected elsewhere in Ash.

For example:

```text
Step<Transaction, Open, Query>
    Next = Open
```

can be supplied by evidence rather than by type-level case analysis.

This keeps user-defined kinds orthogonal to general type-level programming.

---

# 21. Interaction with session types

The immediate motivating use is protocol state.

For example:

```ash
kind TxState =
    Idle
    | Open
    | Closed
```

allows a direct representation:

```text
Session<Transaction, Idle>
Session<Transaction, Open>
Session<Transaction, Closed>
```

Transitions can then be expressed as:

```text
begin :
    Session<Transaction, Idle>
    -> Session<Transaction, Open>

query :
    Session<Transaction, Open>
    -> Session<Transaction, Open>

commit :
    Session<Transaction, Open>
    -> Session<Transaction, Closed>
```

This improves developer experience without making session types a primitive feature.

The harder session-type problem remains resource multiplicity and stale endpoint reuse.

Kind declarations solve the naming and indexing problem, not the usage-discipline problem.

---

# 22. Interaction with resource multiplicity

Finite static kinds may also provide natural domains for resource properties.

For example:

```ash
kind Multiplicity =
    Linear
    | Affine
    | Unrestricted
```

allowing types such as:

```text
Resource<File, Open, Linear>
```

or:

```text
Continuation<OneShot>
```

This is useful even if multiplicity ultimately becomes intrinsic type-system machinery rather than an ordinary type index.

The kind declaration mechanism should not prejudge where multiplicity semantics belong.

It merely provides a natural way to name finite static modes where such indexing is appropriate.

---

# 23. Other likely uses

The same mechanism may be useful for:

```text
protocol states
resource states
multiplicity modes
continuation modes
handler modes
workflow phases
permissions
calling conventions
representation choices
compiler-visible modes
```

This broader applicability is important.

A `kind` declaration should not be justified only as session-type syntax.

It should represent a general notion of a finite nominal static domain.

---

# 24. Expected type-checker impact

For the initial form, the core type-checking machinery should require little new theory.

Likely additions include:

```text
declaration elaboration
    allocate KindId
    allocate static constructor identities
    populate environments

name resolution
    resolve kind names
    resolve static constructors

kind checking
    accept new Atom(KindId) values

variables
    permit rigid/inference variables of user-defined kinds

quantification
    relax the current Type-only policy where explicitly allowed

unification
    reuse existing kind-preserving rules

type application
    reuse existing kind-directed application
```

No higher-order unification is required.

No dependent type checking is required.

No type-level evaluation is required for the basic form.

---

# 25. Promotion implementation impact

Restricted promotion should occur during declaration elaboration.

Conceptually:

```text
promote T

1. resolve T
2. inspect its declaration
3. check Promotable(T)
4. derive corresponding static kind
5. derive corresponding static constructors
6. establish promotion correspondence metadata
```

The ordinary kind checker need not know whether an atomic kind was written directly or produced by promotion.

This preserves the rule:

> **Promotion is an elaboration feature, not a new type-checking mechanism.**

---

# 26. Diagnostics

Because the feature is deliberately restricted, diagnostics should explain which unsupported shape prevented a declaration or promotion.

For example:

```text
cannot promote Option

promotion currently requires every constructor
to have no payload

constructor Some has payload A
```

or:

```text
kind constructor Succ may not take arguments

user-defined kinds currently support only
finite nullary alternatives
```

Diagnostics should state the semantic restriction directly rather than suggesting that the declaration is malformed in general.

This leaves room for the language to expand the accepted forms later.

---

# 27. Initial evidence required

A first implementation should demonstrate at least the following.

### Direct finite kind

```ash
kind State =
    Idle
    | Open
    | Closed
```

introduces three static constructors of kind `State`.

### Kind-directed application

A type constructor expecting `State` accepts:

```text
Session<Open>
```

and rejects:

```text
Session<Int>
```

### Inference variable solving

```text
?S : State
```

may solve to `Open` but not `Int`.

### Rigid variables

A quantified or otherwise bound:

```text
S! : State
```

remains rigid.

### Nominal distinction

Two separately declared finite kinds are not interchangeable.

### Promotion success

```ash
type State =
    Idle
    | Open
    | Closed

promote State
```

produces the same usable static shape as a direct kind declaration.

### Promotion failure

A datatype with constructor payloads is rejected by the initial promotion rule.

### Session-state example

A simple state-indexed API reads naturally and kind-checks correctly.

### Namespace diagnostics

Ambiguous or colliding names produce understandable errors.

---

# 28. Initial non-goals

The first version should not require:

```text
kind polymorphism
higher-rank kind polymorphism
parameterized user-defined kinds
constructor payloads in kind declarations
recursive static data
general datatype promotion
promotion of arbitrary runtime values
type-level lambdas
type-level pattern matching
dependent elimination
singleton synthesis
automatic reflection
automatic reification
full dependent typing
```

These may be investigated independently if future pressure requires them.

---

# 29. Open questions

The semantic core appears small.

Most unresolved questions are likely in the surface language and namespace model.

Important questions include:

### Declaration syntax

Should finite static domains use:

```ash
kind State =
    Open
    | Closed
```

or another form?

### Promotion syntax

Should promotion be:

```ash
promote State
```

an annotation on the type declaration, or another construct?

### Shared names

Should runtime and promoted static constructors intentionally share source spelling?

### Qualification

Should:

```text
State.Open
```

be available or required?

### Type/kind namespace

May an unrelated `type State` and `kind State` coexist?

### Promotion identity

Are runtime and static constructors distinct compiler identities linked by metadata, or two roles of one declaration identity?

### Empty kinds

Should finite kinds eventually permit zero inhabitants?

### Richer shapes

Which concrete pressure would justify payload constructors, parameterized kinds, or recursion?

These questions should be answered from actual use cases rather than by copying another language's promotion model.

---

# 30. Design discipline

The important architectural separation is:

```text
kind declaration
    introduces a static domain

promotion
    derives such a domain from compatible runtime data

kind checking
    validates static use

type-level relations
    describe transitions or computation over those domains
```

These should not collapse into one feature.

In particular:

```text
user-defined kinds
    != kind polymorphism

promotion
    != dependent typing

finite static domains
    != general type-level computation
```

The initial design should preserve these distinctions.

---

# 31. Main hypothesis

The current hypothesis is that Ash can obtain most of the developer-experience benefit associated with datatype promotion by introducing a substantially smaller feature:

> **Nominal finite user-defined kinds with nullary static constructors, plus optional promotion of runtime datatypes having the same admissible shape.**

This would make state-indexed APIs visually natural:

```text
Session<Transaction, Open>
```

without requiring artificial nominal state types and without committing Ash to general term-to-type lifting.

The type-checking machinery appears to require only modest extension because the current representation already supports arbitrary atomic kinds, kinded variables, and kind-directed application.

The major design work is instead expected to concern:

```text
surface grammar
declaration forms
namespaces
constructor resolution
promotion correspondence
diagnostics
```

The guiding implementation test is:

> **Can user-defined finite static domains enter Ash by extending declaration elaboration and semantic policy while leaving the existing core notions of kinds, type application, variables, and unification intact?**

If so, this is a relatively small feature with potentially broad value for session types and several other future Ash abstractions.