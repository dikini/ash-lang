# CP-0034: Top-Level Declaration and Derive Macros

- ID: `CP-0034`
- Status: accepted
- Related: [DN-0062](../design/DN-0062-hygienic-surface-macros.md),
  [expression-syntax specification](../../spec/syntax-expansion.md),
  [first-slice design](../design/macros/first-slice.md),
  [declaration cases and prospective delivery](../design/macros/declaration-slice.md),
  [declaration grammar](../design/macros/declaration-grammar.md),
  [derive authoring and grammar design](../design/macros/derive-syntax.md).

> This proposal is accepted but not implemented. It builds on the implemented
> expression-syntax slice and does not yet describe current Ash. Product work
> also requires an owning task and an authorized delivery base.

## Current behavior

The current [module grammar](../../spec/syntax.md#grammar) admits imports,
syntax definitions and ordinary module declarations. Imported expression
syntax can be invoked in expressions; declaration-position macros and derive
clauses are not part of current Ash.
[Name resolution](../../spec/name-resolution.md#imports-and-namespaces)
establishes module imports and declaration identities before resolving bodies.

The [expression-syntax slice](../../spec/syntax-expansion.md) provides
declarative templates and checked Ash transformers without declaration or
derive output. This proposal builds on that retained contract.

### Slice 1 reconciliation

CP-0034 preserves CP-0033's explicit syntax imports, definition and caller
contexts, checked Ash transformer host, syntax handles, origins, bounded
execution and ordinary checking of expanded programs. It extends their use to
top-level declarations and derive subjects; it does not replace the expression
macro contract. The [reconciliation record](../design/macros/declaration-slice.md#slice-1-contract-boundary)
maps these shared boundaries to the slice 2 additions and fixtures.

The retained expression slice checks template syntax at definition and resolves
surviving literal free names in their defining environment at expansion. Issued
contexts and ordinary resolution enforce access without separate per-reference
grant objects. Its host admits checked monomorphic `Input -> MacroResult`
transformers, transfers authenticated output before teardown, and preserves
ordinary errors and origins. Its public `Node` and `Capture` sums are closed;
`TokenKind` and its spellings are now specified in
[lexical structure](../../spec/lexical-structure.md#public-token-kinds).
These are the expression baseline, not evidence that generated module-level
binders or generator adapters already work.

Slice 2 implementation is confined to parsing, syntax transformation and
their supporting helpers. Macros transform syntax and produce code; they are
not responsible for proving that the produced code is valid or for repairing
it. The ordinary parser and downstream compiler detect and report errors in
that code. The macro subsystem checks its own notation and preserves source
contexts, spans and origins so those errors can be traced to their sources.
Name resolution,
duplicate and visibility checks, type and effect checking, evidence selection,
elaboration, publication, linking and Core validation belong to their existing
downstream subsystems. Preserve source contexts, spans and expansion origins so
those subsystems can report their own errors. Keep slice 1's syntax-handle
admission and host boundaries; they do not establish semantic correctness.

Do not duplicate or approximate a downstream check in macro machinery, even if
the compiler currently misses a case. Record any downstream gap with a
reproducer, expected behavior and affected subsystem as a separate downstream
issue; stop dependent work until it is resolved or explicitly rescheduled, and
continue independent work. This proposal does not authorize changes to the
downstream subsystem. Any change to the proposed language contract returns to
CP-0034 for a design decision. The proposed public-name behavior must still be
checked against the existing pipeline; slice 1 does not yet support declaration
output.

## Proposed behavior

### Reserved word `syntax`

Reserve `syntax` throughout Ash. It cannot be used as a user-defined
identifier, including a term, module-path segment, import alias or syntax
name. It remains the keyword used for syntax declarations and imports. This
allows a quotation form beginning with `syntax` without treating an ordinary
identifier or an imported macro of that name as a quotation. The existing
compiler-owned module path `@builtin.compiler.syntax` remains valid; its final
segment is not a user-defined identifier.

This is a deliberate compatibility change: programs that currently use
`syntax` as an identifier must rename it. Other identifiers, including
`declaration`, retain their existing status. The proposed quotation and escape
forms are described below.

Extend the existing closed `Syntax.TokenKind` sum with `SyntaxKeyword` for
`syntax` and `Dollar` for `$`. The existing `make_token` and `token_kind`
operations use those exact spellings. This lets ordinary quoted expressions
survive traversal through the existing syntax service; delimiters remain
structured groups, and identifier nodes retain their contexts. A dollar
token in syntax data is not itself an instruction to expand an outer template.
Ordinary parsing still rejects it where it has no syntactic role. Existing
exhaustive `TokenKind` matches must account for the two new cases.

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
The companion specifies the affected sums. Slice 1 defines no selectable or
recorded syntax-interface version, so this proposal assumes no such mechanism.
Changed constructor sets can require source consumers to update and be checked
again; cross-version artifact policy is a separate language-interface concern.
These public sums remain closed; generator outputs use syntax rather than an
open conversion interface.

A generator returns syntax directly. For an expression splice, the step has
the ordinary type `State -> (State, Syntax.ExpressionFragment)`. For example:

```text
next_number : Int -> (Int, Syntax.ExpressionFragment)
```

The argument is the current state: `from` supplies the first state, and the
first returned component supplies the next. The second returned component is
the fragment inserted into the template. Helpers may have any ordinary Ash
types; only the step's final result must have the stated pair type. Pure
generator functions are the expected case. If a function uses an effect
row, including a row variable where ordinary Ash permits one, ordinary Ash
checking and the existing slice 1 host rules apply. This proposal adds no
generator-specific effect rule.

Two authoring paths have been selected: a syntax subtemplate, parsed and filled
with its variables, and procedural syntax construction in ordinary Ash code.
Both produce an expression fragment and preserve its syntax context and origin.
They use the existing syntax admission and diagnostic behavior; they do not
perform semantic analysis. There is no generic conversion interface or
implicit conversion from an `Int` value. General-purpose conversion libraries
are outside this slice.

Any ordinary Ash function with the required state-to-pair type can be used as
the step. The compiler checks its type using ordinary Ash rules; the macro
system threads its state and substitutes the returned fragment. It does not
inspect how the function constructs that fragment or require a conversion
interface. I17 provides both a subtemplate graph and a procedural graph that
selects quote-created fragments using the syntax service. It does not
demonstrate fresh fragment construction from raw syntax.

#### Syntax admission and failures

Use the same syntax checks and diagnostics as slice 1 at their existing
boundaries:

- Parse a syntax subtemplate when its containing source definition is compiled.
  This includes a subtemplate inside an ordinary generator or helper function.
  Report malformed subtemplate syntax then, even if no macro later invokes that
  function. Fill its holes during expansion; syntax admission checks the
  resulting fragment without resolving or type-checking generated Ash.
- Procedural construction uses the existing syntax parsing behavior. In slice
  1, `parse_expression` returns `Parsed(fragment)` or
  `ParseRejected(failure)`. A procedural transformer can handle a failure or
  return `Rejected(SyntaxDiagnostic(failure))` to preserve its structured
  cause. Construction from a generator must use the same syntax and
  diagnostic path, not a new error model.
- After substitution, parse and admit the complete macro output as ordinary
  declaration syntax. A syntax error rejects the expansion without publishing
  partial output. Generated declarations that parse then pass to the existing
  downstream compiler for name, type and other semantic checks.

When a generator calls an operation that returns a fallible result, its
ordinary Ash code handles that result according to its declared return type.
A generator need not introduce a separate error protocol. Syntax failures at
definition and output admission continue through the existing macro diagnostic
path. The generator itself follows its ordinary declared Ash type.

The step is an ordinary Ash function checked as part of compiling its defining
module. Because declaration macros are imported, that module is already
checked when another module invokes the macro. The expander does not inspect
or independently verify the function's body or type. An invocation-supplied
seed and any generated call are subject to ordinary Ash checking in the
appropriate existing environment; an incompatible use remains an ordinary Ash
error. Preserve the relevant source contexts and spans for that error.

Execute checked seed and step calls through the slice 1 transformer host.
Reuse its bounded execution, syntax services,
handle validation and diagnostic propagation. Check caller-supplied seed
expressions in the caller's available compile-time environment, using ordinary
Ash checking. An internally generated Ash
adapter is one possible implementation, not a language requirement. A step has
the ordinary shape `A -> (A, B)`: its input is the current state, and its output
contains the next state followed by the generated value. No macro `Input`
argument or ambient input operation is needed to connect the seed and step. The
macro machinery threads the returned state into the next call and substitutes
the returned value at the generator's repetition scope.

The generated declarations pass through ordinary resolution and type checking.
The macro expander does not perform a separate type analysis of generators,
their uses, or generated code, and does not extend the ordinary type checker.
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
bindings retain their respective contexts. As in retained slice 1,
ordinary imports and the `using` transformer target are still checked as
definition dependencies. Ordinary Ash checking and error propagation handle
generated-program meaning.

An introduced implementation method head first uses the binding in its
authenticated syntax context. If that complete context has no term binding for
the head, the head selects the same-named method of the implemented interface.
Ordinary source heads, collisions, access and interface membership retain their
existing rules.

A declaration-macro capture binding may use a reserved word as its metaname
after `$`; its declaration template may read that capture using the same
spelling, including in repetitions. This does not change keyword lexing,
the identifiers consumed by `ident` captures, expression-macro matchers,
derive or generator binding names, or ordinary escaped-code and quotation
variables.

Declarative matching supports the companion's caller-selected declaration name
and type captures. Variable-length derives use procedural syntax traversal;
the declarative derive form binds the subject name. Implementation must not
assume a matcher's spelling is an identity test or depend on inferred types,
selected implementations, compiler IR, or unchecked private declarations.

### Executable template escapes and expression subtemplates

The escape and subtemplate design in this section is accepted with CP-0034;
this syntax is not yet current Ash. A template describes the syntax it emits.
`${ ... }` marks ordinary Ash code to run while filling that template. It
contains either an ordinary block or one inline result expression; the
resulting syntax value is inserted at the escape's position.
The initial form admits the already specified protected fragment categories:
`Syntax.ExpressionFragment`, `Syntax.TypeFragment`, `Syntax.PatternFragment`,
`Syntax.DeclarationFragment`, and an identifier together with its
`Syntax.Origin`. It introduces no implicit conversion or new syntax-value
interface. The existing output parser admits or rejects the resulting syntax
at its position; for example an expression fragment in a type position fails
syntax admission. Ordinary Ash checking handles the escaped code and its
result. Other result categories and raw declaration sequences are not added by
this form.

```ash
pub syntax declaration: (define_plus) $name:ident from $value:expr => {
    pub $name : Unit -> Int
    $name () = ${
        let input = $value
        syntax { $input + 100 }
    }
}
```

Given `define_plus answer from 5`, the output is equivalent to a function
`answer () = 5 + 100`. The `let` is expansion-time code and is not emitted.
A `syntax { expression }` expression selects an expression subtemplate with
the intended `Syntax.ExpressionFragment` result. Its braces delimit the
expression syntax rather than adding a block. The macro subsystem constructs
the fragment from the quoted syntax as the ordinary function executes, using
the existing checked host and syntax-handle boundaries. It may use internal
syntax transformation helpers; the function needs no compiler `Input` argument
or special function category. Inside the quote, `$input` splices the fragment
held by the ordinary Ash variable `input`. A quote can contain another
`${ ... }` escape, whose code can construct another quote. Protected fragment
boundaries preserve precedence across insertions.

On 2026-11-09, the user accepted the inline result-expression alternative in
this proposal. An escape is `$` followed either by an ordinary Ash block or by
braces containing exactly one expression. If the next token after `{` is a
logical line end, parse the ordinary block. Otherwise, parse one expression
and require the matching `}` without a logical line end at the escape's own
level. Nested parentheses, braces and blocks follow the existing expression
and logical-line rules. The inline form has no outer local-declaration list;
ordinary block syntax is unchanged.

A quote is a `primary_expression` of the form `syntax { ... }` containing
exactly one expression with fragment-valued `$name` holes and `${ ... }`
escapes; it can occur wherever an ordinary primary expression is admitted. The
quote's outer braces delimit its content. Parse these forms by the token after
`$`: `{` begins an escape, `(` begins a template repetition only in existing
repetition-enabled macro templates, and a macro name begins a splice or capture
reference according to the surrounding mode. Expression quotes do not add a
new repetition form.

Inside escaped code, `$value` reads the lexically enclosing macro's capture as
an Ash value, not as code to evaluate or text to re-lex. Its type follows the
capture kind:

| Capture | Ash value |
| --- | --- |
| `expr` | `Syntax.ExpressionFragment` |
| `type` | `Syntax.TypeFragment` |
| `pattern` | `Syntax.PatternFragment` |
| `declaration` | `Syntax.DeclarationFragment` |
| `ident` | `(Syntax.Identifier, Syntax.Origin)` |

Each value retains its syntax context and source origin. Capture access is
lexical: an ordinary helper called by an escape does not acquire the caller's
capture names. Pass any needed value as an ordinary argument. A `$name` in a
quote inside escaped code splices an ordinary Ash variable, not a macro capture;
bind a capture to a variable first, as above.

Existing repetition scope applies. An escape inside a template repetition sees
the current selected values at that depth; a capture cannot be read outside the
repetition scope required for its remaining levels. Capture reads in escaped
code count as uses when determining the surrounding template repetition's
existing drivers. Multiple drivers retain the existing matching-length rule;
nested repetitions select their current values in the existing order. This form
does not add a way to read an entire repeated capture outside its existing
scope; the procedural syntax service retains `RepeatedCapture(Captures)` and
its nested grouping. Generator bindings in scope may be read inside escaped
code as their syntax values, with the same per-iteration stepping, nesting and
cached reuse as ordinary template splices; generator reads do not themselves
supply a repetition driver. `from $start` remains the existing seed expression
and its existing caller-context checking, not an escape capture-value read.

An outer macro template processes its `$name` splices recursively through
ordinary nested groups and quotes, as in slice 1. A quote simply written as
part of that outer template does not establish a new splice scope, and an
unknown outer splice still fails. A `${ ... }` encountered there executes as
an escape of that outer template. Entering an escape changes mode: its code is
ordinary Ash with lexical capture-value reads. A `syntax { ... }` evaluated in
that code constructs a subtemplate with its own ordinary-Ash-variable holes.
An escape in that subtemplate executes when the subtemplate is constructed and
can construct another subtemplate. Thus the escape boundary, not mere nested
braces, separates the stages.

Parse escapes and quotes with their containing definition; reject malformed
notation, including a malformed unused quote, there. Ordinary Ash compilation
checks executable code, names, calls, hole variable types and results in their
lexical environments. Literal free names written as quoted output follow slice
1's deferred resolution when surviving generated code is checked. Each reached
escape executes once in source order when its containing template is filled;
escapes in zero repetitions and unused definitions do not execute. Use the
existing checked host, handle authentication, bounds and failure propagation.
A failed escape rejects the complete invocation without publishing partial
output.

Literal quoted identifiers retain the quoting definition's context and a fresh
introduction for each quotation construction, as in slice 1. Literal syntax
retains its construction origin. Captured and spliced syntax retains its own
contexts, protected boundaries and origins; copied fragments follow slice 1's
existing copy rules. Origins do not confer authority. Preserve macro
invocation and definition frames for diagnostics. Syntax admission checks
fragment placement; downstream compiler stages check the generated program. No
macro-specific semantic checker, new generator conversion interface, implicit
primitive conversion, new error protocol or user-visible compiler `Input`
parameter is added.

The state-only generator contract remains `State -> (State,
Syntax.ExpressionFragment)`. The quote specifies the subtemplate source form
and its macro-subsystem construction. The independently reviewed I17 procedural
variant uses syntax-service operations on quoted fragments; it does not
demonstrate constructing a fresh fragment from raw syntax.

Required evidence: the [I22 source fixtures](../design/macros/fixtures/escapes/README.md)
cover all five capture categories,
capture-versus-local names, an escape's use as a repetition driver, current
iteration and generator cached values, nested repetitions and subtemplates,
zero iterations, independent macro invocations and hygiene, precedence,
definition-time malformed unused quotes, executable ordinary type errors,
wrong fragment positions, retained diagnostics and atomic failure. Check the
reserved-word cases and `@builtin.compiler.syntax` path. Exercise these through
the public compiler path after implementation; none is a passing product test
until then.

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
existing parse and meaning except for the newly reserved `syntax` word. The
initial corpus fixes generated-subject,
derive-order and definition-time template cases; their agreement with this
contract remains subject to independent review before acceptance.

Spliced caller identifiers keep caller lexical and syntax context. A
caller-supplied binder can introduce a declaration referenced by caller source;
its public visibility follows the emitted declaration. Local binders inside a
generated declaration retain slice 1's existing hygiene rules.

Generated top-level names, whether private or public and whether written by the
macro or supplied by its caller, follow ordinary module namespace and duplicate
rules. If declarations conflict, including across macro invocations or with a
handwritten declaration, the unchanged downstream compiler reports the
conflict. Syntax transformation does not detect, resolve or silently rename it.
Preserve enough source spans and expansion origins for the diagnostic to
identify both conflicting declarations and their relevant macro invocations.
The author or caller controls which names the macro emits; passing distinct
names is one way to avoid conflicts. A future or proposed helper may produce
unique spellings under a clearly stated scope, but this decision does not add
a helper or assume that a fresh syntax context alone changes a spelling.

An introduced `pub` name is intended to be accessible by its written spelling
to the invoking module and, subject to ordinary visibility, its importers.
Whether this works through unchanged downstream resolution remains an
acceptance question. Deliberately constructed caller-context names use slice
1's explicit context operation and remain subject to normal collision and
visibility rules.

Definition-site references retain their issued syntax context. Ordinary
resolution uses that context to select the defining environment and enforce
its access and import rules; linking retains the necessary checked closure.
They do not import an implementation into the caller, grant access to another
module's withheld member, or grant builtin authority. The retained slice 1
contract uses no separate per-reference grant objects; this proposal does not
reintroduce them.
Generated declarations use the normal namespace, opacity, duplicate,
implementation-evidence, type, effect, resource, and independent Core
validation rules, without changes to those downstream stages. Imports and
ordinary caller syntax do not gain access to the macro owner's private helpers.
Generated public names and implementation facts enter the caller's checked
public summary under the established module rules. Ordinary duplicate errors
are the intended result for conflicting generated names. Access to literal
public names through unchanged resolution remains to be demonstrated; otherwise
record a downstream resolution issue and return any contract change to the
design owner.

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
- Reserve `syntax` as a keyword; existing uses of that word as a user-defined
  identifier must be renamed. Preserve other existing no-syntax program behavior,
  subject to the compatibility rule for candidate source notation.

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
The local [delivery plan](../design/macros/slice2-delivery-plan.md) preserves
the earlier 126- and 130-point predictions and estimates the current scope at
150 points, with 142 remaining. The new prediction accounts for executable
escapes, token changes and their connected evidence. C4 source preparation and
C3 independent review are recorded as complete. Points predict difficulty;
they are not measured results or an acceptance decision.
The I17 [fixture record](../design/macros/fixtures/generators/README.md) fixes
the expected behavior and construction coverage. Both source graphs are
written but have not run. The procedural graph selects fragments
created by quotation; it does not demonstrate fresh fragment construction
from raw syntax. The selected generator type and construction approaches
remain unchanged.
Implementation requires an owning task and authorized delivery base. C3
reviewed the proposed grammar, syntax-service contract and integration corpus
against the retained CP-0033 result; review subsequent substantive changes as
needed. Handwritten controls and limited stand-ins have run; the proposed macro
paths are not passing product tests.

The final implementation must execute the accepted integration corpus through
the real public compiler driver, interpreter and supported build/image path;
run positive, negative, scope, module and mutation cases; retain useful human
and structured diagnostics; and pass independent review, the required fresh
workspace gate and the owning task's acceptance audit. Tests may be added as
new cases are discovered, but cannot weaken the agreed starting corpus.
