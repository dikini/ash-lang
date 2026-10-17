# Ash Specification

This directory is the canonical Ash specification. It is normative and
describes exactly the implemented language and runtime behavior.

## Current Ash

Ash is a rank-1 language whose programs are acyclic graphs of passive source
modules. Each `.ash` source file defines one unnamed module containing
imports followed by nominal data or `newtype` declarations, method-only
interface declarations, effect declarations, anonymous implementation
declarations, scalar foreign-library declarations, and global function
definitions. Global signatures may state
explicit interface constraints and latent effect rows, and implementation
heads may state explicit prerequisite constraints. A module has no result
expression, runtime module value, or initialization.

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
constructor family. The corresponding `newtype` visibility modes use the same
name and constructor access rules.

A module `newtype` introduces a nominal type over one representation. It has
exactly one same-spelled, one-field constructor. Construction and matching are
explicit, and the nominal type remains distinct from its representation.
After independent Core validation, wrapping and unwrapping erase without a
wrapper allocation or runtime tag. Interface evidence remains nominal: an
implementation for the representation does not satisfy a requirement for the
`newtype`.

A local `newtype` introduces one compile-time lexical identity for the
following declarations and result of its block. Its representation sees the
preceding type scope; later declarations may shadow the nominal and constructor
names together. The identity cannot escape in a type, effect row, scheme, or
requirement. A closure may capture and unwrap a local value when its exposed
computation contains no such identity. Execution creates no fresh identity or
scope state.

A sequential local `with` supplies exact interface methods for a complete
application whose selection key contains an active local nominal. It is not
local implementation search. Supplied methods capture preceding ordinary values;
the evidence is available only in the following lexical remainder. Selected
methods lower to ordinary functions, and checked closures may retain them
after that evidence block returns without exporting the evidence itself.

An interface declares one or more ordered, fixed-kinded type parameters and an
ordered set of method signatures. It may declare one total forward
determination edge from a nonempty parameter key to the entire dependent
complement. A method may bind an explicit ordered list of fixed-kinded local
parameters, and every method value type has `Function` as its top-level
constructor. Each occurrence instantiates the complete interface vector and
the method parameters, while only the complete interface application creates
an evidence obligation. Its methods are constrained terms. An implementation
supplies the complete method set for one complete interface application but
introduces no source name. Private implementations remain available only in
their defining module; `pub impl` publishes a body-free fact that dependents or
later facades may select explicitly. Body-free summaries preserve canonical
interface parameter and determination records, complete applications, method
schemes, and their defining identities.

Ash's monomorphic kind language contains `Type`, `EffectRow`, and
right-associative function kinds such as `Type -> Type`. Declaration parameters
may state their kinds.
Every omitted declaration kind annotation and every binder introduced by an
omitted implementation binder list is fixed to `Type`. An omitted global
binder list discovers ordinary free type variables and effect-row-tail
variables in their shared first-occurrence order. A name occurring only in
ordinary type positions has kind `Type`; one occurring only as an effect-row
tail has kind `EffectRow`; using the same name in both roles is invalid. Ash
does not infer a function kind from use. This is a phase-dependent constraint,
not a commitment against later bounded declaration-local kind inference. A
type constructor or parameter may remain bare or partially applied when its
resulting kind satisfies the context that owns the type.

An effect declaration defines one module-owned API with one or more operations.
Function computations carry rows of exact, parameterized effect identities.
`perform` requests an operation, and an exhaustive lexical `handle` removes one
exact instance. Each selected clause must consume its non-escaping continuation
capability exactly once on every normally completing path, with `resume` or
checked `discard`. Discard closes the selected capture and recursively owned
live captures in structural order, then continues the clause with `Unit`.
Inference proves safe closure without skipping outside or running completion
owners. Its effect row includes invoked cleanup actions.

An owner-free `foreign library` declaration supplies passive ABI facts
and exact native effects with one `call` operation each. Complete ordered
`Type` and `EffectRow` parameters and original contracts survive publication
and imports. `@builtin.foreign` supplies ordinary common result types,
including `Call<T>` and opaque `ConversionError`. Compilation installs an
explicit checked Core interpretation for admitted owner-free native entry
instances, leaving an empty outward row. Ordinary source handlers cannot
install a native symbol's interpreter. Source contracts and checked Core supply
no executable binding; default execution refuses missing bindings before Ash
runs. Checked scalar literal constants publish ordinary mathematical `Int`
values and supply exact declared native operands. A declared `function_address`
sentinel supplies only a fixed all-bits-one native operand; it publishes no
ordinary value and grants no call permission. Copy windows remain outside
the admitted subset. Source resource declarations admit opaque and
initialized byte owners with declared dependencies, private data and checked
`scope` or `acquired_only` reports. Their owner families retain complete ordered
Type/Row arguments with a Type-kind owned identity and support one
acquisition and `void` or scalar-status finish and host-destruction contracts
with total consumed or retained dispositions. Scalar status predicates use
checked literal facts from the original owner library; the predicate itself
grants no value or operand authority. Retention revokes ordinary access and
quarantines the same
owner and dependency closure; safe host destruction preserves dependency order.
Ordinary pure module-global helpers may transform independent lifecycle payloads,
including through same-module and imported polymorphic definitions. Their complete
Type/Row instances and original copied calls remain checked; they cannot carry
native State or acquire native permission. Privileged lifecycle wrappers and
library migrations remain unsupported. Checked
lexical forwarding supports the associated interface methods and ordinary
constrained helpers, preserving exact operation types, effect rows and typed
access operands. Sealed common byte reads and writes borrow the exact
initialized live state in acquire, handler and finish phases. Original call
correspondence, complete Type/Row instances and the unique guard authenticate
access; private data and a compatible state type grant no permission.
Conversion refusals are ordinary `Foreign.Call` results, and complete reply
admission precedes native access. Outward capture/resume moves the same source
owner; owned discard runs required finish computations in structural order with
needed outer resources live, without an abandoned result wrapper. Running
completion cannot be abandoned. Acquisition discard revokes an unpublished
guard without fabricating private data. Exact constructor and native-call
identities authenticate publication and completion; declarations alone confer
no ownership. The [source-resource
rules](static-semantics.md#source-resource-declarations) bound this lifecycle
and its supported associated handler shape.

`resource cell<R> c = initializer { body }` acquires one scoped mutable integer
cell through the compiler-owned `@builtin.cell` API. The scope owns release;
handles provide reusable access while it remains live. Inferred dependencies
prevent handles, captured access and identity-indexed operations from escaping
their owner, including through request payloads. Copied integers may escape.
Each execution has a fresh activation, and capture/resume moves the owned
scope without duplication. Normal completion or owned abandonment releases it
once.

The ordinary passive [native-buffer library](../libraries/native_buffer.ash)
uses `resource Buffer.Buffer<R> b = length { body }` after an explicit import.
Its Ash acquisition, associated handlers and finish use common checked foreign
contracts, bytes, guards and the `acquired_only` codec. Positive lengths acquire
zeroed writable bytes; invalid lengths refuse before C. Acquisition returns
ordinary `Failure(Error)` without a body, or releases normally and returns
`Success(body_value)`. Nested outcomes remain nested. Capture/resume moves the
same owner; owned discard completes it once without the abandoned wrapper.
Generated hosts execute the native calls. The old builtin module, lowercase
resource designator and fixed evaluator adapter are removed; cell semantics
remain unchanged.

`hook H { body }` supplies the empty identity chain for an exact effect API
with one endomorphic `publish` operation. `register H transformer { body }`
evaluates one ordinary transformer and retains it for that scope. Publication
uses `perform H.publish value`; outer registrations transform before inner
ones, and callbacks run under handlers surrounding their registration. An exact
nested root starts a separate chain. Normal return removes each registration
once; capture/resume preserves its owner. Owned abandonment removes it without
running its transformer or remaining publication callbacks; discard cannot
skip required outside completion. Callback effects and stored resource
dependencies remain checked.

`cleanup action { body }` evaluates and retains one `Unit -> Unit` action.
Normal completion invokes it, then returns the saved body value unchanged.
Capture/resume transfers the invocation owner; copies of the callable gain no
cleanup authority. Owned abandonment invokes actions under the surviving
context with needed live resource handlers. Ordinary source handlers removed by
the cut are not restored.
Required removed interpreters reject at each action's closing position.
An executing action and its unfinished close operation remain required
completions and cannot be discarded. Action effects and stored dependencies
remain checked. Ordinary typed reporting can retain ordered cleanup failures
separately from the body outcome; constructors have no implicit failure meaning.
Internal termination or exhaustion provides no source-cleanup guarantee.

The source path selected for execution is the entry module. It declares exactly
one local, monomorphic, unconstrained `main : Unit -> R`, where `R` is closed.
Its computation row is empty. After checking every dependency, Ash links the
module definition groups and evaluates `main ()`.
Imports, exports, aliases, and opacity are static access rules and do not remain
as runtime operations. Interface identities, implementation identities, and
their checking registries also erase. Selected evidence lowers to ordinary
functions, applications, and dialect-specific type operations. Pure erases
instantiation; Effect retains lexical instantiation for exact operation
matching across generic calls and returned closures. Evaluation has no runtime
module object, implementation registry, interface lookup, or handler registry.

Ordinary source value positions remain rank-1.
No source annotation denotes a nested scheme. Source code cannot write
`forall` or expression type arguments; give a parameter, result, tuple field,
or constructor field a polymorphic annotation; store or return an
uninstantiated method scheme; pass one to an ordinary parameter; add implicit
method binders or method requirements; or use polymorphic recursion.
Core admits a nested scheme only where authenticated compiler-generated method
evidence requires it. Every other source value position remains monomorphic;
the internal lexical polymorphic functions retained by Effect execution do not
make schemes first-class source values.

Determination adds no associated-output syntax or projection, multiple or
partial edges, proposition or proof evidence, common universal evidence, or
existential pack and unpack form.

Module and local `newtype` add no runtime-fresh identity,
implicit coercion, general representational equality, local implementation,
effect or resource mechanism, existential package, dynamic loading, runtime
nominal registry, heap-inspection API, special value rendering, or general ABI
or foreign-representation guarantee. Its canonical conversion establishes no
interface, proof, provider, handler, or hook authority.

Within a module, Ash provides global and explicit local recursion, rank-1
polymorphism, nominal data, allocation-free module and local `newtype`, structural tuples, constructor values, typed
patterns, exhaustive matches and equations, sequential bindings, method-only
interfaces, explicit constraints, anonymous implementations, and pure and
effectful expressions with single-use, non-escaping handler continuations.

Beyond the fixed builtin providers and the bounded source-resource forms
described above, the effect kernel adds no general provider or resource
declarations, first-class registration tokens, arbitrary removal or priorities,
general destructor declarations, escaping or multi-shot resume, asynchronous
execution, or dynamic loading.
A linked nonempty effect row is a source rejection rather than an
unhandled-operation runtime result.

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

### Module newtypes

This complete module wraps and unwraps a distinct nominal `UserId`. The wrapper
has the integer representation at runtime, so the program observes the value
`42` while retaining the result type `UserId`:

```ash
newtype UserId = UserId(Int)

increment : UserId -> UserId
increment (UserId value) = UserId(value + 1)

main : Unit -> UserId
main () = increment(UserId(41))
```

The executable test `overview_module_newtype_example_is_executable` checks this
example. Neither constructor use is an implicit conversion, and an importer
may use the constructor only through a transparent authorized route.

### Local newtypes

This complete module returns a closure that captures a local representation,
then calls it after `make` returns. The closure exposes only `Unit -> Int`, so
the program observes `42 : Int` without exposing the local identity:

```ash
make : Unit -> (Unit -> Int)
make () = {
    newtype Offset = Offset(Int)
    let offset = Offset(41)
    fn(ignored) {
        match offset {
            Offset(value) => value + 1
        }
    }
}

main : Unit -> Int
main () = make()()
```

The executable test `overview_local_newtype_closure_example_is_executable`
checks this example. Local declarations are sequential and private; they do
not add local implementations or implicit existential packages.

### Scoped exact evidence

This complete module supplies the relation `Read<Token, Int>` for a local
identity. The supplied method captures `saved`; `forward` receives its ordinary
method function through the existing constraint mechanism. The result is
`42 : Int`:

```ash
interface Read<A, B> where A -> B {
    read : A -> B
}

forward<A, B> : A -> B where Read<A, B>
forward value = read(value)

main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    let saved = Token(41)
    with Read<Token, Int> {
        read ignored = match saved {
            Token(value) => value + 1
        }
    }
    forward(saved)
}
```

The test `overview_scoped_evidence_example_is_executable` checks this example
and the direct `read(saved)` variant. Abstract requirements and exact-current
implementation evidence precede lexical evidence; lexical evidence precedes
concrete implementation matching. This form introduces no resource lifetime,
proof authority, acquisition, or existential package.

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

### Polymorphic method evidence

One constrained global may use the same method scheme at unrelated
instantiations. This `api.ash` module exports a higher-kinded interface whose
method binds two local type parameters, then uses it once from `Int` to `Bool`
and once from `Bool` to `Int`:

```ash
pub interface Functor<F : Type -> Type> {
    map<A, B> : (A -> B, F<A>) -> F<B>
}

to_bool : Int -> Bool
to_bool value = value == 42

to_int : Bool -> Int
to_int true = 42
to_int false = 0

pub map_pair<F : Type -> Type> : (F<Int>, F<Bool>) -> (F<Bool>, F<Int>) where Functor<F>
map_pair (numbers, flags) = (map((to_bool, numbers)), map((to_int, flags)))
```

The sibling `carrier.ash` module reuses the defining method identity and
publishes a generic implementation for `Box`:

```ash
pub import api (Functor, map)

pub type Box<A> = Box(A)

pub impl Functor<Box> {
    map (function, Box(value)) = Box(function(value))
}
```

A total determination edge permits a dependent parameter to occur anywhere or
nowhere in a method type, while every determinant must occur. Improvement uses
an inference-free key to fill the whole dependent tuple before complete-
application evidence selection. This program determines `Result` as `Unit`
from the `Bool` key even though `Result` is absent from `measure` and observes
`42 : Int`:

```ash
interface Measure<Key, Result> where Key -> Result {
    measure : Key -> Int
}

impl Measure<Bool, Unit> {
    measure value = 42
}

main : Unit -> Int
main () = measure(true)
```

The `entry.ash` module imports the constrained global and explicitly selects
the implementation:

```ash
import api (map_pair)
import carrier (Box, impl Functor)

main : Unit -> (Box<Bool>, Box<Int>)
main () = map_pair((Box(42), Box(true)))
```

The program observes:

```text
(Box(true), Box(42)) : (Box<Bool>, Box<Int>)
```

The method scheme is authenticated across both source-body-free summaries.
Concrete evidence uses one generated adapter over the implementation method;
this Pure program erases its type operations through the existing evaluator
rules. The source filename retained by the test corpus is `interface.ash`, but
the executable tree stages that content as `api.ash` because `interface` is reserved in
a module path.

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
