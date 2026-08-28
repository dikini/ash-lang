# Ash Specification

This directory is the canonical Ash specification. It is normative and
describes exactly the implemented language and runtime behavior.

## Current Ash

Ash is a pure, rank-1 language whose programs are acyclic graphs of passive
source modules. Each `.ash` source file defines one unnamed module containing
imports followed by nominal type declarations, method-only interface
declarations, anonymous implementation declarations, and global function
definitions. Global signatures may state explicit interface constraints, and
implementation heads may state explicit prerequisite constraints. A module has
no result expression, runtime module value, or initialization.

Imports expose only public facts. A private complete import places a
dependency's public namespaces under a module alias. A private targeted import
places selected public spellings in the importing module's file-wide
namespaces. A public import must be targeted and re-exports its selected
spellings. These name channels preserve the defining declaration identities.

An `impl Interface` item is an independent channel. It binds no source name and
makes the dependency summary's public implementations for that interface
available for evidence selection. Neither a complete import nor a targeted
name item selects implementations. A public implementation item also adds the
selected facts to the importer's public implementation closure, so later
facades can select them transitively without changing their defining
identities. Private nominal identities may flow through public schemes and
implementation facts without becoming nameable. A `pub opaque type` exports a
name without constructors, and a `pub type` exports its name and complete
constructor family.

An interface declares one type parameter and an ordered set of method
signatures. Every method type has `Function` as its top-level constructor. Its
methods are constrained terms. An implementation supplies the complete method
set for one interface argument but introduces no source name. Private
implementations remain available only in their defining module; `pub impl`
publishes a body-free fact that dependents or later facades may select
explicitly.

Ash's monomorphic kind language contains `Type` and right-associative function
kinds such as `Type -> Type`. Declaration parameters may state their kinds.
Every omitted declaration kind annotation, and every binder introduced by an
omitted global or implementation binder list, is fixed to `Type`; Ash does not
infer a function kind from use. This is a phase-dependent constraint, not a
commitment against later bounded declaration-local kind inference. A type
constructor or parameter may remain bare or partially applied when its
resulting kind satisfies the context that owns the type.

The source path selected for execution is the entry module. It declares exactly
one local, monomorphic, unconstrained `main : Unit -> R`, where `R` is closed.
After checking every dependency, Ash links the module definition groups and
evaluates `main ()`.
Imports, exports, aliases, and opacity are static access rules and do not remain
as runtime operations. Interface identities, implementation identities, and
their checking registries also erase. Selected evidence lowers to ordinary
functions and applications; evaluation has no runtime module object,
implementation registry, or interface lookup.

Within a module, Ash provides global and explicit local recursion, rank-1
polymorphism, nominal data, structural tuples, constructor values, typed
patterns, exhaustive matches and equations, sequential bindings, method-only
interfaces, explicit constraints, anonymous implementations, and pure
expressions.

## Module examples

The following two sibling files form a complete program. `main.ash` imports
`./arithmetic.ash` under the alias `Arithmetic`:

```ash
import arithmetic as Arithmetic

main : Unit -> Int
main () = Arithmetic.answer(())
```

`arithmetic.ash` exports only `answer`:

```ash
pub answer : Unit -> Int
answer () = 42
```

Kinds and higher-kinded parameters also cross module boundaries. This
`dependency.ash` file exports a kinded interface, an implementation for the
bare `Option` constructor, and a global whose explicit parameter has kind
`Type -> Type`:

```ash
pub type Option<A> =
None
| Some(A)

pub interface Observe<F : Type -> Type> {
observe : F<Int> -> Int
}

pub impl Observe<Option> {
observe value = 40 + 2
}

pub relay<F : Type -> Type> : F<Int> -> F<Int>
relay value = value
```

The sibling entry imports the nominal, constructor, constrained method,
polymorphic global, and selected implementation fact:

```ash
import dependency (Option, Some, observe, relay, impl Observe)
main : Unit -> Int
main () = observe(relay(Some(1)))
```

The dependency summary carries the defining identities and fixed kinds without
the dependency body. Linking authenticates the selected `Observe<Option>`
evidence before Core synthesis. The program observes `42 : Int`; kinds and
selected interface evidence introduce no runtime lookup or module value.

A targeted import can select and rename that export without introducing a
module alias:

```ash
import arithmetic (answer as imported_answer)

main : Unit -> Int
main () = imported_answer(())
```

### Interfaces and selected evidence

An interface method can use a local implementation without changing the entry
contract. This complete module selects `Equal<Int>` at the call to `equal` and
observes `true : Bool`:

```ash
interface Equal<A> {
    equal : (A, A) -> Bool
}

impl Equal<Int> {
    equal (left, right) = left == right
}

main : Unit -> Bool
main () = equal(1, 1)
```

Constraints also cross module boundaries through checked public declarations.
In the following sibling-file program, `main.ash` uses a complete import for
qualified names and a separate targeted item for implementation evidence:

```ash
import equality as Equality
import equality (impl Equal)

main : Unit -> Bool
main () = Equality.same((1, 1))
```

The defining `equality.ash` exports a method-only interface, a constrained
global, and an anonymous implementation fact:

```ash
pub interface Equal<A> {
    equal : (A, A) -> Bool
}

pub impl Equal<Int> {
    equal (left, right) = left == right
}

pub same : (A, A) -> Bool where Equal<A>
same pair = equal pair
```

The body of `same` uses its declared requirement. At the imported call,
ordinary typing fixes the argument to `Int`, and the explicit selector makes
the defining module's public implementation available. The program observes
`true : Bool`.

A targeted public import can place a facade between that implementation owner
and the entry. This complete `facade.ash` re-exports names and implementations
through independent items:

```ash
pub import equality (Equal, equal, impl Equal)
```

The facade entry selects the same channels from `facade.ash`:

```ash
import facade (Equal, equal, impl Equal)

main : Unit -> Bool
main () = equal(1, 1)
```

The selector follows the facade's public authorization route to the
implementation defined in `equality.ash`. The interface, implementation,
method, and binder identities remain those of the defining module. Aliases and
authorization routes do not become runtime values; the selected method
evidence runs as ordinary function application.

### Opaque types and smart constructors

An opaque type is nameable in an importer, but its constructors are not. This
`token.ash` module keeps construction and matching inside its boundary:

```ash
pub opaque type Token = Token(Int)

pub make : Int -> Token
make value = Token(value)

pub step : Token -> Token
step (Token value) = Token(value + 1)

pub read : Token -> Int
read (Token value) = value
```

An importer may name `Token.Token` in an annotation and compose the public
operations. It cannot use the `Token` constructor in a term or pattern:

```ash
import token as Token

main : Unit -> Int
main () = {
    let token : Token.Token = Token.make(41)
    Token.read(Token.step(token))
}
```

### Hidden carriers

A private type can occur in public function schemes without exporting its
source name. In `carrier.ash`, the identity shared by `make`, `step`, and `read`
remains consistent for importers:

```ash
type Hidden = Hidden(Int)

pub make : Int -> Hidden
make value = Hidden(value)

pub step : Hidden -> Hidden
step (Hidden value) = Hidden(value + 1)

pub read : Hidden -> Int
read (Hidden value) = value
```

An importer can infer a local carrier and pass it among compatible operations.
It cannot name that carrier in an annotation or global signature:

```ash
import carrier as Carrier

main : Unit -> Int
main () = {
    let hidden = Carrier.make(41)
    Carrier.read(Carrier.step(hidden))
}
```

### Transparent matching

A public transparent type exports its complete constructor family. For example,
`choice.ash` exports `Choice`, `First`, and `Second`:

```ash
pub type Choice =
    First(Int)
    | Second(Int)

pub sample : Unit -> Choice
sample () = First(42)
```

Importers can construct and match those constructors, and coverage checks use
the complete exported family:

```ash
import choice as Choice

main : Unit -> Int
main () = match Choice.sample(()) {
    Choice.First(value) => value
    Choice.Second(value) => value + 1
}
```

## Specification chapters

The specification is split by concern:

- [Lexical structure](lexical-structure.md) defines admitted source text,
  tokens, whitespace, and logical line boundaries.
- [Syntax](syntax.md) defines module, import, declaration, expression, and
  pattern grammar, precedence, and associativity.
- [Name resolution](name-resolution.md) defines module identity, import and
  export access, lexical scope, and binder identity.
- [Static semantics](static-semantics.md) defines dependency-ordered module
  checking, exported schemes, entry checking, and expression typing.
- [Elaboration](elaboration.md) defines how checked modules and surface
  presentations converge on one linked typed Core program.
- [Dynamic semantics](dynamic-semantics.md) defines values and deterministic
  evaluation of the generated entry application.

The [`ash` tool documentation](../docs/tools/ash.md) describes invocation,
module-root configuration, output, diagnostics, and exit status. Those are tool
behaviors, not additional language semantics.

## Change discipline

Future behavior belongs in [design notes](../docs/design/README.md) and
[change proposals](../docs/proposals/README.md), not here. A language change
updates this specification in the same merge as the implementation and tests
that make the new statements true. Partially implemented or intended behavior
must not appear here.
