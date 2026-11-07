# CP-0034: Top-Level Declaration and Derive Macros

- ID: `CP-0034`
- Status: proposed
- Related: [DN-0062](../design/DN-0062-hygienic-surface-macros.md),
  [CP-0033](CP-0033-hygienic-expression-syntax.md),
  [first-slice design](../design/macros/first-slice.md),
  [declaration cases and prospective delivery](../design/macros/declaration-slice.md),
  [declaration grammar](../design/macros/declaration-grammar.md),
  [derive authoring and grammar design](../design/macros/derive-syntax.md).

> This is a working proposal, not current Ash or implementation authority.
> It depends on CP-0033 being implemented and retained. The candidate source
> syntax and unresolved contracts in the companion need review before this
> proposal can be accepted. The slice 1 definition-context and name-timing
> amendments are in progress; their eventual retained contract is a dependency.

## Current behavior

The current [module grammar](../../spec/syntax.md#grammar) admits imports
followed by ordinary module declarations. It has no source macro invocation or
derive. [Name resolution](../../spec/name-resolution.md#imports-and-namespaces)
establishes module imports and declaration identities before resolving bodies.

Accepted CP-0033 proposes imported expression syntax, declarative templates and
checked Ash transformers; it does not add declaration or derive output. Its
implementation is in progress and has not become current specification truth.
This proposal builds on that slice and must be reconciled with its actual
retained contract before implementation.

### Slice 1 reconciliation

CP-0034 preserves CP-0033's explicit syntax imports, definition and caller
contexts, checked Ash transformer host, syntax handles, origins, bounded
execution and ordinary checking of expanded programs. It extends their use to
top-level declarations and derive subjects; it does not replace the expression
macro contract. The [reconciliation record](../design/macros/declaration-slice.md#slice-1-contract-boundary)
maps these shared boundaries to the slice 2 additions and fixtures.

Two CP-0033 amendments are still in the slice 1 delivery rather than the
accepted proposal on the main branch. The current accepted text checks free
template names when the macro is defined and requires per-reference grants.
The user-directed amendment instead checks template syntax at definition,
resolves surviving free names in the defining environment on expansion, and
uses issued contexts and ordinary resolution without separate grant objects.
CP-0034 below follows that amended direction. Until the slice 1 amendment and
implementation are reviewed and retained, those two rules are a dependency,
not a retained CP-0033 contract. The final reconciliation must compare this
proposal and its fixtures with the actual retained result.

## Proposed behavior

### Scope and output

A module may invoke an explicitly imported declaration macro in a module
declaration position; it cannot invoke its own syntax definitions, following
CP-0033. A successful invocation emits an ordered sequence of
complete ordinary module declarations, possibly through nested declaration
invocations that are expanded before admission. A `deriving` clause on a
top-level `type` or `newtype` selects one or more derive macros. Each receives
the subject declaration and emits zero or more additional ordinary declarations;
the original type remains once. Deriving is not available on other declaration
forms. A failed expansion publishes neither the subject nor partial derive output.

The common output parser admits every existing module declaration category:
`type`, `newtype`, `interface`, `impl`, `effect`, `foreign library`, and both
global-function forms. Their ordinary modifiers, headers, nested syntax, and
admission rules remain applicable. The exact examples, edge cases and required
programs are in the [case catalogue](../design/macros/declaration-slice.md#declaration-catalogue).
The output is an ordered sequence of declarations, not source text to re-lex.
An empty declaration-macro output is admitted. A declaration fragment must
contain complete declarations and no import, syntax declaration, recovery
node, missing node, or trailing unparsed token.

Imports and module identity are fixed before expansion. A macro cannot create
an import, import item, source file, module, syntax definition, syntax import,
or syntax re-export. Local declaration-position and type- or pattern-position
macro invocations are outside this proposal. Existing expressions inside an
emitted declaration may contain ordinary CP-0033 expression invocations.

### Candidate source notation

The following notation is a candidate for review, not implemented Ash:

```text
import common (Marker, mark)

pub syntax declaration: (identity) $name:ident for $T:type => {
    pub $name : $T -> $T
    $name value = value
}

pub syntax declaration: (computed) $name:ident => using expand_computed

pub syntax derive: (marker) $target:ident => {
    impl Marker<$target> {
        mark _ = true
    }
}
```

`syntax declaration: (name)` identifies a declaration-macro definition;
`declaration` remains an ordinary identifier elsewhere. The parenthesized name
distinguishes this form from a CP-0033 expression macro named `declaration`:
slice 1 permits `:` as a matcher literal but does not permit matcher groups.
Braces after `=>` delimit the declaration template and are not themselves
output. A declaration macro is selected by its imported leading name in a
module declaration position. Derive definitions use `syntax derive: (name)`;
the subject-name binding above supplies the type or newtype name. The working
deriving notation is:

```text
import generators (syntax identity, syntax marker, syntax display)

identity id for Int

pub type Color = Red
    | Blue
    deriving (marker, display)

pub newtype Count = Count(Int)
    deriving (marker)

main : Unit -> Int
main () = id 42
```

The clause follows the type or newtype on a new logical line and lists derive
names in parentheses, separated by commas. Each listed name selects an imported
derive macro; it is not an interface name unless that name also selects a
derive macro. The [derive authoring design](../design/macros/derive-syntax.md)
records the approved working forms, derive-specific grammar and disambiguation.
The overall proposal remains subject to review and acceptance.

The mechanics follow [Rust's derive macros](https://doc.rust-lang.org/reference/procedural-macros.html#derive-macros):
the macro receives the item and produces additional items, commonly interface
implementations. Ash uses a deriving clause in place of an attribute and applies
the existing Ash syntax-context and checked-expansion rules.

Repetition uses `*` for zero or more and `+` for one or more occurrences.
Captures repeated together in a template must have matching lengths and are
consumed in order; repetitions may nest and preserve their capture structure.
The [declaration grammar](../design/macros/declaration-grammar.md) defines
matchers, repetition drivers and failure rules. A declaration
invocation ends at the logical line boundary, with
balanced groups allowed to span lines; captures must be complete in their
syntactic categories. A captured declaration is delimited by braces, allowing
its ordinary multi-line syntax inside the invocation.

### Transformer data and traversal

Declarative and procedural implementations share the same checked, bounded
expansion and output admission. The syntax service needs a protected type
fragment and a protected complete-declaration fragment, and operations to
inspect their ordered syntax without discarding contexts, spelling or origins.
A derive receives the complete subject as an authenticated capture. A
procedural transformer can traverse balanced syntax, construct ordinary
declarations and reject a shape it does not support. The exact public Ash
constructors and operation signatures for declarations are listed in the
[declaration syntax service](../design/macros/declaration-slice.md#declaration-syntax-service).
Neither a Rust AST nor a compiler-internal enum is public API.

The working choice is to extend slice 1's existing closed public syntax sums
where declaration syntax requires additional cases. Existing consumers must
be updated where their exhaustive matches no longer cover the extended sums.
The companion specifies the affected sums and requires rebuilding artifacts
whose syntax-interface version differs. An interface for generator-produced
fragments can coexist with these closed sums; it does not make them open.

The working generator API uses an ordinary Ash `SyntaxFragment<F>` interface
whose `fragment_node` method converts a fragment and an origin to a `Node`.
Its expression-fragment implementation returns the existing `ExpressionNode`;
the extended syntax service also supports type, pattern and complete-declaration
fragments. Interface implementations do not grant scope or visibility: the
existing handle authentication, syntax admission and hygiene rules still apply.

Check seed and step calls using ordinary Ash rules and execute them through the
slice 1 checked transformer host. Reuse its bounded execution, syntax services,
handle validation and diagnostic propagation. Select generator interface
evidence in the macro definition's environment without importing that evidence
into caller code; check caller-supplied seed expressions and their evidence in
the caller's available compile-time environment. An internally generated Ash
adapter is one possible implementation, not a language requirement. A step has
the ordinary shape `A -> (A, B)`: its input is the current state, and its output
contains the next state followed by the generated value. No macro `Input`
argument or ambient input operation is needed to connect the seed and step. The
macro machinery threads the returned state into the next call and substitutes
the returned value at the generator's repetition scope.

Ordinary Ash checking checks generator functions and their return types. The
generated declarations then pass through ordinary resolution and type checking;
the macro expander does not perform a separate type analysis of generated code.
Syntax admission still rejects malformed output and fragments in the wrong
syntactic position.

A generator is declared in a `with` clause following a template or template
repetition. Its clause initializes it once per invocation when attached to the
whole template, or once per iteration when attached to a repetition. An
iteration that consumes a generated value advances the generator once; repeated
uses in that iteration share the value. Ordinary Ash type checking establishes
that the seed, step argument, returned state and generated value are compatible;
there is no separate generator type checker. A generator may take its initial state
explicitly from a macro invocation. A seed written in the definition's `with`
clause is a separate choice and does not add an invocation argument. Generator
binding names are unique within one macro definition; duplicate names are
rejected rather than shadowed. Ordinary Ash checking checks seed and step
types, including an invocation-supplied seed. The companion specifies
initialization, source-order stepping and per-iteration reuse at nested levels.
At declaration expansion, a caller-supplied seed may use inline expressions
and checked imports, but cannot depend on the caller module's own globals,
which have not yet been checked. Reject such a reference with a staging
diagnostic. A definition-site seed can use its already checked defining-module
helpers and dependencies. Widening the caller's available globals is deferred.

At definition time, parse the template and check macro-notation bindings,
including capture and generator names and repetition structure. Do not resolve
template-written free names then: an unused template may contain an unknown
free name. When an invocation produces that reference, ordinary resolution
uses the definition-site environment and reports an unavailable name there;
a same-spelled caller name cannot supply it. Captured syntax and introduced
bindings retain their respective contexts. As in slice 1's amended candidate,
ordinary imports and the `using` transformer target are still checked as
definition dependencies. Ordinary Ash checking and error propagation handle
generated-program meaning.

Declarative matching supports the companion's caller-selected declaration name
and type captures. Variable-length derives use procedural syntax traversal;
the declarative derive form binds the subject name. Implementation must not
assume a matcher's spelling is an identity test or depend on inferred types,
selected implementations, compiler IR, or unchecked private declarations.

### Staging, names and authority

Resolve explicit syntax imports from the fixed acyclic dependency graph.
Declaration and derive syntax are distinct entry forms. Expand them in source
order before ordinary module resolution: expand a declaration invocation when
encountered, and apply a subject's derives when its clause is encountered,
before proceeding to later source declarations. For a subject with several
derives, invoke them left to right on the same original subject; then process
their generated declarations in output order, including any nested macros or
derives. Retain the subject once followed by the ordered output. The first
expansion failure in that order is reported. This does not constrain how the
compiler schedules ordinary parsing or downstream semantic diagnostics.
Derives do not read inferred types or implementation selection, and expansion
does not reopen a checked dependency body. Nested expression expansions use
CP-0033. Nested declaration invocations use the syntax imports of their source
context and the existing bounded expansion policy. Declaration collection
precedes body resolution, allowing
ordinary forward and recursive references. Fresh identities must be
deterministic modulo renaming, and ordinary no-macro modules retain their
existing parse and meaning. Generated derive subjects and definition-time
validation need complete rules and fixtures before acceptance.

Spliced caller identifiers keep caller lexical and syntax context. A
caller-supplied binder can introduce a declaration referenced by caller source;
its public visibility follows the emitted declaration. Introduced binders and
their references share the macro introduction context and cannot accidentally
capture caller names. Separate invocations have separate introduced helpers.
An introduced `pub` name is accessible by its written spelling to the
invoking module and, subject to ordinary visibility, to its importers. Public
names collide under the ordinary module rules, including across expansions.
Private introduced binders retain hygienic isolation. Deliberately constructed
caller-context names use CP-0033's explicit context operation and remain
subject to normal collision and visibility rules.

Definition-site references retain their issued syntax context. Ordinary
resolution uses that context to select the defining environment and enforce
its access and import rules; linking retains the necessary checked closure.
They do not import an implementation into the caller, grant access to another
module's withheld member, or grant builtin authority. Slice 1's in-progress
amendment removes separate per-reference grant objects; this proposal does not
reintroduce them. The amended slice 1 contract must be retained before this
proposal is implemented.
Generated declarations use the normal namespace, opacity, duplicate,
implementation-evidence, type, effect, resource, and independent Core
validation rules. Imports and ordinary caller syntax do not gain access to
macro-private helpers. Generated public names and implementation facts enter
the caller's checked public summary under the established module rules.

Retain invocation, definition, input and construction origins through parsing,
checking, linking and diagnostics. Invalid subject, matcher and output errors,
transformer rejection/failure, ordinary generated-program rejection and
compiler inconsistency remain distinguishable. Scope and origins are separate;
diagnostic locations do not grant authority.

## Semantic delta

- Add explicitly imported top-level declaration and derive invocations with
  declarative and checked Ash authoring forms.
- Add declaration and type syntax interchange, structural access and ordered
  declaration output, without exposing compiler ASTs or inferred types.
- Extend contextual hygiene, origin propagation and definition-context
  resolution to generated module declarations and their checked exports.
- Preserve existing no-syntax program behavior, subject to an explicitly
  specified compatibility rule for the candidate contextual source notation.

## Affected specification areas

- [Lexical structure](../../spec/lexical-structure.md#tokens), including the
  shared public token vocabulary if additional kinds are needed.
- [Grammar](../../spec/syntax.md#grammar), module declarations, imports,
  declaration fragments and selected invocation syntax.
- [Name resolution](../../spec/name-resolution.md#imports-and-namespaces),
  [declaration identities](../../spec/name-resolution.md#interface-implementation-and-requirement-identities),
  module scope, visibility, imports and generated export identity.
- [Static semantics](../../spec/static-semantics.md#globals-and-modules),
  syntax service admission, ordinary declarations and implementation evidence.
- [Elaboration and validation](../../spec/elaboration.md#validation-boundary),
  generated declarations, checked dependency closure and independent Core
  validation; compiler and diagnostic documentation.

The parser decision must be reviewed for declaration-position syntax, without
silently introducing arbitrary parser callbacks or changing recovery and
projection invariants.

## Resulting specification truth

After the complete transition is retained and integrated, Ash specifies the
implemented top-level declaration and derive forms, their syntax service and
their scope, origin and admission behavior. Generated output is checked as
ordinary Ash. CP-0033 expression behavior remains independently applicable.

## Interactions

Effects and resources use their own currently applicable contracts. This
proposal does not reconcile with, depend on, or provide the semantics of their
redesign. An interface-specific derive is a syntactic generator of ordinary
implementations; it cannot establish unexpressed control, ownership,
completion, one-shot, or evidence properties.

## Non-goals

- Local declaration macros, macros producing imports or syntax definitions,
  arbitrary grammar callbacks, or macro-defined module files.
- Arbitrary imported-declaration reflection, inferred-type queries, typed
  compiler transformations, Core generation, or unrestricted ambient services.
- Whole-function continuation rewriting, language-syntax retirement, effects
  redesign, self-hosting, or a browser/Wasm implementation.

## Required evidence

The companion records the historical 65- and 95-point predictions alongside
the declaration inventory, integration catalogue and dependency-ordered tasks.
The updated scope requires a new estimate once its remaining choices and the
slice 1 contract are settled.
Implementation requires a separately accepted proposal and owning task. Before
acceptance, independently review the proposed grammar, syntax-service contract,
integration corpus and remaining semantic decisions against the retained
CP-0033 result, and resolve findings. Handwritten controls and limited
stand-ins have run; the proposed macro paths are not passing product tests.

The final implementation must execute the accepted integration corpus through
the real public compiler driver, interpreter and supported build/image path;
run positive, negative, scope, module and mutation cases; retain useful human
and structured diagnostics; and pass independent review, the required fresh
workspace gate and the owning task's acceptance audit. Tests may be added as
new cases are discovered, but cannot weaken the agreed starting corpus.
