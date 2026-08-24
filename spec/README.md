# Ash Specification

This directory is the canonical Ash specification. It is normative and
describes exactly the implemented language and runtime behavior.

## Current Ash

Ash is a pure, rank-1 language whose programs are acyclic graphs of passive
source modules. Each `.ash` source file defines one unnamed module containing
imports followed by nominal type declarations and global function definitions.
A module has no result expression, runtime module value, or initialization.

Imports expose only declarations marked `pub`. A complete import places a
dependency's public namespace under a module alias; a targeted import places
selected public spellings in the importing module's file-wide namespaces.
Private nominal identities may flow through public function schemes without
becoming nameable. A `pub opaque type` exports a name without constructors, and
a `pub type` exports its name and complete constructor family.

The source path selected for execution is the entry module. It declares exactly
one local, monomorphic `main : Unit -> R`, where `R` is closed. After checking
every dependency, Ash links the module definition groups and evaluates
`main ()`.
Imports, exports, aliases, and opacity are static access rules and do not remain
as runtime operations.

Within a module, Ash provides global and explicit local recursion, rank-1
polymorphism, nominal data, structural tuples, constructor values, typed
patterns, exhaustive matches and equations, sequential bindings, and pure
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

A targeted import can select and rename that export without introducing a
module alias:

```ash
import arithmetic (answer as imported_answer)

main : Unit -> Int
main () = imported_answer(())
```

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
It cannot name that carrier in an annotation or global interface:

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
