# Top-level declaration and derive macros: working design

This companion develops [CP-0034](../../proposals/CP-0034-top-level-declaration-macros.md).
It accompanies an accepted but unimplemented proposal and contains a
prospective delivery map, not an active task or current Ash. The expression
slice is implemented and retained. Recheck its contract before fixing declaration
producer/consumer interfaces or dispatching work.
Use the [working issue-planning rules](../../project/issue-planning.md) when
revising the delivery breakdown.

## Objective and difficulty

Allow Ash-authored macros to emit ordinary top-level declarations and derives
to inspect a supplied declaration and emit additional declarations. Use syntax
rewriting; the existing resolver and checker establish meaning. Exclude local
declaration invocations, generated imports and syntax definitions, typed
reflection and whole-function CPS conversion.

The fixed first prediction is **65 difficulty points**. These are relative
engineering judgments, not time, probabilities, or a claim that points are
already earned. The reference is the slice 1 delivery's 100-point estimated
ledger, which was incomplete at observation; it is not measured model effort.
The functionality and task allocations below both total 65. Record predicted
and observed difficulty separately; a changed forecast does not rewrite the
prediction. Record a genuine scope change explicitly.

The generator-assisted templates and the change to type and newtype deriving
clauses add scope after the 65-point prediction. Their separate estimate is
30 points, making the revised scope **95 points**. The original prediction is
retained rather than rescaled. The incremental tasks and acceptance assertions
appear below; predicted and actual difficulty remain separate. The independent
review identified grant-specific work not required by the retained expression
slice and implementation choices that remain open. The 95 points are the
recorded pre-review prediction, not a fresh estimate for the revised contract.
The [local delivery plan](slice2-delivery-plan.md) records the later 126-point
prediction, the later 130-point forecast and the current 150-point scope
prediction, including 142 points of remaining delivery work.

| Functionality | Points | Counted once |
| --- | ---: | --- |
| Declaration invocations and ordinary output | 14 | Matching, category-preserving construction and every current top-level output form. |
| Derive invocations and structural work | 12 | Retained subject, shape access and variable-length derives. |
| Procedural declaration bridge | 7 | Checked Ash input, output and host boundaries for both categories. |
| Module scope, hygiene and publication | 20 | Staging, generated identities, contextual access and exported declarations. |
| Diagnostics, end-to-end evidence and delivery | 12 | Cross-cutting diagnostics, product-path tests, docs, QA, review and gates. |
| **Original subtotal** | **65** | |
| Generator-assisted templates | 23 | Grammar, state, checked calls, diagnostics and generator-specific evidence. |
| Deriving-clause additions | 7 | Clause disambiguation, multi-derive expansion and subject-name binding. |
| **Revised total** | **95** | |

The declaration design includes a procedural bridge because slice 1 already
owns a checked transformer host and the declaration path needs shared output
admission regardless. Define its concrete API against the corpus. A small
closely related follow-up should be included rather than made into another
delivery by default.

## Declaration catalogue

These examples are **ordinary output targets**, not claims that the proposed
macro syntax is implemented. Each is one complete declaration except the
equational global, whose signature and equations form one declaration. The
[grammar](../../../spec/syntax.md#grammar) remains authoritative for current
Ash. The rightmost column fixes initial coverage; it does not permit the macro
engine to introduce separate language rules for these forms.

| Form and target example | Required cases and corners | Corpus |
| --- | --- | --- |
| `type`: `pub type Color = Red` | Single and multiple constructors on separate logical lines; generic parameters and payloads; public, private and `pub opaque`; supplied type and constructor binders; duplicate constructor/type; malformed separator. | I01, I08, I10 |
| `newtype`: `pub newtype Box<A> = Box(A)` | Generic and nongeneric, public/private/opaque; type and constructor have the same required spelling but distinct identities; mismatched constructor, invalid representation and access to an opaque constructor. | I02, I08, I10 |
| `interface`: `pub interface Marker<A> { mark : A -> Bool }` | Multiple methods; interface and method parameters and kinds; optional determination; duplicate method and malformed method type. | I03, I08 |
| `impl`: `impl Marker<Color> { mark _ = true }` | Empty and multiple equations where ordinary rules admit them; generic parameters, constraints, multiple method clauses; duplicate/conflicting or incomplete impl and missing evidence. | I04, I09, I11 |
| `effect`: `pub effect Ask { ask : Unit -> Int }` | Generic/nongeneric; multiple operations; operation names scoped by effect; duplicate operation and invalid type. These are current-effect regression cases, not an effects redesign. | I05, I08 |
| `foreign library`: `pub foreign library Fixture { profile "x86_64-unknown-linux-gnu" ... }` | Profile and symbol strings, qualified types, multiple symbols; missing/duplicate profile and malformed symbol. Check public availability and ordinary foreign admission; never execute a foreign call merely to test syntax. | I06, I08 |
| Equational global: `pub id : Int -> Int` followed by `id value = value` | Signature and multiple equations remain one declaration; generic parameters, constraints and patterns; missing or mismatched equation and bad body. | I07, I08 |
| Inline global: `pub fn id(value: Int) -> Int { ... }` | Parameters/patterns, return type, optional constraints and multiline block; invalid binder, type or body. | I07, I08 |

Output modifiers and constructor/method/operation sequences are parsed by the
ordinary category grammar. Matchers expose identifier, type, expression,
pattern and declaration captures. A separate token-tree capture is not part of
these declaration decisions; output coverage alone does not imply it.

## Candidate syntax and contract

CP-0034 illustrates declaration syntax imported with the existing `syntax`
selector. The prior `derive syntax name ... { declaration }` wrapper is
superseded: a deriving clause belongs on a `type` or `newtype`, follows the
declaration on a new logical line, and lists derive names in parentheses. The
[derive authoring design](derive-syntax.md) records the approved working
grammar, disambiguation and definition syntax. A
declaration template's outer braces delimit the template rather than emitting
a block expression. The working definition header uses
`syntax declaration: (name)` and leaves `declaration` available as an ordinary
identifier elsewhere. The parenthesized name distinguishes the new form from
an expression macro named `declaration`, because CP-0033 permits a `:` literal
but not matcher groups. Identifier, type, expression, pattern and
declaration captures are specified in the companion grammar. The compatibility
fixture covers ordinary globals and CP-0033 expression imports.

The proposed [declaration grammar](declaration-grammar.md) gives the complete
definition, matcher, repetition, template and generator forms, including the
termination and disambiguation rules. It remains to be checked against the
retained slice 1 implementation and the complete integration programs.

An imported declaration syntax name selects its matcher at module-declaration
position. A declaration template's enclosing braces do not form output. The
companion grammars specify invocation and deriving clauses on generated types.

For the first concrete comparison, use these prospective rules: a declaration
matcher contains named captures separated by literal tokens. A non-final
capture ends at its next literal at the current syntactic level; a final
capture ends at the module-level logical line boundary. Balanced inner groups
belong to the capture. A declaration capture is delimited by braces and may
span logical lines within them. The category parser must accept the complete captured fragment with
no recovery node. Adjacent captures and ambiguous stopping literals are
definition or invocation errors. The final EBNF must refine these rules
without silently claiming compatibility with every CP-0033 matcher.

Repetitions use `$( ... )*` for zero or more and `$( ... )+` for one or more,
with a separator such as `,` between the closing group and operator when
needed. Repetitions may nest, and the captured sequence retains its nesting
and source order. Each matcher capture name is unique within the macro;
generator names cannot collide with matcher capture names. An iteration must
consume input, and a matcher whose stopping point is ambiguous is rejected at
definition time. There is no fallback to an ordinary declaration after the
imported syntax name selects a matcher.

A template repetition is driven by captures at its corresponding repetition
depth. Captures used together there must have matching lengths, and each
iteration selects the corresponding captured elements in source order. Nested
lengths are checked within their containing iteration. A template cannot use a
repeated capture outside its matching repetition or repeat without a driver.
A zero-length `*` emits no repeated output; an empty match for `+` fails.
Captured fragments retain their syntactic boundaries and contexts when spliced.

The CP-0033 service is the baseline to retain; it exposes Ash data and
authenticated handles rather than a compiler AST. The declaration extensions
and compatibility rule are specified below; the indexed fixture provides a
complete transformer body. The shared lexical vocabulary remains subject to
the independent-implementation contract recorded by CP-0033.

The slice 1 `Capture`, `CaptureResult`, `Node` and `Syntax` families are ordinary
public nominal data that procedural transformers may exhaustively match. The
working choice is to extend existing closed sums where declaration syntax needs
new cases, and update their compiler-provided and Ash consumers. Identify the
affected types and constructors rather than assuming every family needs an
extension. Existing matches without a suitable fallback may need new cases even
when expression behavior is unchanged. Use explicit cases where their meaning
matters; a wildcard is appropriate only when ignoring future cases is correct.
Slice 1 exposes no selectable or recorded syntax-interface version. No
versioned-artifact mechanism is assumed by this proposal. Consumers must be
checked against the constructor set they use; cross-version artifact policy is
a separate language-interface concern. No automatic compatibility of
exhaustive source matches is assumed.

### Slice 1 contract boundary

The retained expression slice checks template syntax at definition, then
resolves surviving free names at expansion in their definition context. Issued
contexts and ordinary resolution enforce access without separate per-reference
grant objects. CP-0034 follows that baseline; its accepted declaration-specific
additions still need implementation and connected evidence.

| Slice 1 boundary | Reuse and slice 2 addition | Initial evidence |
| --- | --- | --- |
| Explicit syntax imports and module staging | Reuse selection and rename rules; add declaration and derive categories without allowing self-use or generated imports. | I20–I21; [header compatibility](fixtures/header_compat/README.md) |
| Contexts and ordinary resolution | Preserve caller and definition contexts, private access and ordinary evidence rules; add generated module binders and public names. Use the retained slice's deferred free-name timing and no separate grants. | I12–I15; [hygiene](fixtures/hygiene/README.md), [diagnostics](fixtures/diagnostics/README.md) |
| Parser and projection | Reuse structured syntax, protected boundaries and the ordinary parser/projection path; add type, pattern and declaration fragments and module output. Do not add per-form semantic verification. | I01–I08, I14, I19; [declarations](fixtures/declarations/README.md), [captures](fixtures/captures/README.md) |
| Checked host and service | Reuse ordinary checked transformers, permitted effect rows, handle validation, bounds, transfer and teardown; extend the closed syntax sums and calls for declaration data. Generator steps thread ordinary Ash state and share the host boundary. | I10–I11, I16–I18; [indexed derive](fixtures/indexed/README.md), [generators](fixtures/generators/README.md), [migration](fixtures/migration/README.md) |
| Origins and diagnostics | Reuse input, construction and expansion origins; add declaration and derive frames while leaving program errors with ordinary checks. | I14–I15; [diagnostics](fixtures/diagnostics/README.md) |

The [current syntax expansion specification](../../../spec/syntax-expansion.md)
and the QA-confirmed slice 1 delivery establish the expression baseline in
this table. `Node` has token, identifier, group and expression cases; `Capture`
has expression and identifier cases. The declaration-specific cases are
accepted but unimplemented; generators return syntax directly without a
conversion interface. The public token constructors and spellings are specified in
[lexical structure](../../../spec/lexical-structure.md#public-token-kinds).
The expression host checks `Input -> MacroResult`, not an arbitrary generator
step. Declaration staging, an adapter for steps and top-level identity behavior
still require evidence. Slice 1 does not prove those additions work unchanged.
The [local plan](slice2-delivery-plan.md#readiness-questions-before-implementation)
records the outstanding checks and the syntax-only implementation boundary.

### Declaration syntax service

The following proposed additions extend the slice 1 public types in
`@builtin.compiler.syntax`. `TypeFragment`, `PatternFragment` and
`DeclarationFragment` are opaque, compiler-issued handles like slice 1's
`ExpressionFragment`. The alternatives shown are added to the existing sums;
the existing alternatives and their meaning remain unchanged.

Add `SyntaxKeyword` and `Dollar` to `TokenKind`, with fixed spellings `syntax`
and `$`. The existing token operations and exhaustive-match migration rules
apply; this extends the closed sum rather than adding a separate syntax API.

```text
pub type Captures = NoCaptures
    | MoreCaptures(Capture, Captures)
```

Add `TypeCapture(TypeFragment)`, `PatternCapture(PatternFragment)`,
`DeclarationCapture(DeclarationFragment)` and `RepeatedCapture(Captures)` to
`Capture`. Add `TypeNode(TypeFragment, Origin)`, `PatternNode(PatternFragment,
Origin)` and `DeclarationNode(DeclarationFragment, Origin)` to `Node`. Add
`ParsedType(TypeFragment)`, `ParsedPattern(PatternFragment)` and
`ParsedDeclaration(DeclarationFragment)` to `ParseResult`.

The existing `capture(Input, Int)` enumerates distinct matcher capture names in
their first source order. For a repeated capture it returns `RepeatedCapture`
at each repetition depth, including an empty list for zero iterations. Its
leaves contain the ordinary capture category; nested captures keep their group
boundaries. Index failure still returns `MissingCapture`.

```text
type_syntax : TypeFragment -> Syntax ! {Ops}
pattern_syntax : PatternFragment -> Syntax ! {Ops}
declaration_syntax : DeclarationFragment -> Syntax ! {Ops}
parse_type : (Input, Syntax) -> ParseResult ! {Ops}
parse_pattern : (Input, Syntax) -> ParseResult ! {Ops}
parse_declaration : (Input, Syntax) -> ParseResult ! {Ops}
```

The syntax accessors preserve ordering, origins and contexts, and do not
consume the handle. Like `expression_syntax`, they remove that fragment's
outer boundary only when explicitly called. Each parse operation accepts
exactly one complete fragment of its category, returns its corresponding
`Parsed...` alternative or the existing `ParseRejected`, and neither expands
macros nor resolves names. A declaration fragment includes a complete
signature and equations where applicable. For a source-written derive subject,
`declaration_syntax` exposes its ordered tokens, identifier nodes and balanced
groups, including the deriving clause and its preceding logical line end;
the module-level terminator after the declaration is not part of the fragment.
Protected fragments introduced by splicing remain protected nodes rather than
being flattened. A declaration transformer returns
the existing `Expanded(Syntax)`; admission checks the resulting ordered
sequence of complete declarations and any nested invocations.

### Generator-assisted templates

The working source choice uses a trailing `with` clause to bind one or more
generators to the immediately preceding template or template repetition. Each
binding uses `from` for its initial state and `step` for an ordinary Ash
function. The clause is a template directive, not emitted Ash, and is distinct
from slice 1's `=> using transformer` form. The proposed grammar is specified
in [declaration grammar](declaration-grammar.md); it is not yet current Ash.

```text
pub syntax declaration: (make_constants) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = match $first {
            true => $number + 100
            false => $number
        }
    )+
} with {
    $number from 0 step next_number
    $first from 0 step is_first
}
```

The step functions are ordinary checked Ash functions run in the macro
definition's compile-time environment. A generator with state type `A` and
value type `B` has a step of type `A -> (A, B)`: each call receives the
current state and returns the next state followed by its generated value.
The `from` expression supplies the first state. The next call receives the
previously returned state; the template splices the returned value. Ordinary
Ash type checking verifies these connections. The generator result is syntax;
for expression splices it is `Syntax.ExpressionFragment`. No separate generator type checker or
macro `Input` argument is needed. The macro machinery's generator-specific
responsibility is to thread each returned state into the next call at the
agreed repetition scope and substitute the corresponding value. For the
example, the first generator produces expression syntax for
successive integers; the second produces expression syntax for true on the
first step and false on later steps. Separate generators have separate states.
The repetition advances each generator once per matched name in source order;
reusing a generated fragment within one iteration does not advance it again.
A clause on the whole template initializes its generators once per macro
invocation. A clause on a repetition initializes its generators for each
iteration of that repetition. For two groups of two names, attaching the
clause to the outer group repetition produces `0, 1, 0, 1`; attaching it to
the whole template produces `0, 1, 2, 3`:

```text
=> {
    $(
        $(
            pub $name : Unit -> Int
            $name () = $number
        )+
    )+ with {
        $number from 0 step next_number
    }
}
```

Each generator instance evaluates its seed once when its owning template or
repetition iteration is entered. Seeds in one `with` clause are evaluated in
source order. A repetition with zero iterations creates no per-iteration
generator instance. The template is traversed in source order. On the first
use of a generator in a template or repetition iteration, call its step with
the current state, retain the first returned element as the next state, and
cache the second element as the fragment for that iteration. Further
uses in that same iteration reuse it. A nested iteration gets its own cached
value and advances the same instance; returning to an outer iteration retains
its cached value. Thus use at different depths is deterministic without
shadowing or a second generator. An unused generator is not stepped.

The host applies its ordinary execution and expansion bounds. A seed or step
failure fails the invocation and publishes none of its output. The diagnostic
retains the cause, invocation and definition, with input and construction origins
where relevant. No extra generator exhaustion protocol is implied by the
`State -> (State, Fragment)` return type.

Generator names are unique within a macro definition. Each binding declares a
distinct generator, and duplicate names in nested `with` clauses are errors
rather than shadowing. This avoids adding another shadowing rule; the same name
may be used independently in different macro definitions.

The initial state may be supplied explicitly by the macro invocation. A seed
written in the definition's `with` clause, as in the example, is instead
fixed there and is not an invocation argument. A matcher may capture the
invocation's seed as an expression and refer to it in `from`, as in this
candidate notation:

```text
pub syntax declaration: (make_numbered) starting_at $start:expr names $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = $number
    )+
} with {
    $number from $start step next_number
}
```

Evaluate that expression as ordinary Ash in its caller context.
The defining module's ordinary compilation checks the step function before an
importer can invoke its macro. An invocation-supplied seed and a generated use
are checked as ordinary Ash in their respective contexts; compiling the defining
module alone cannot establish that every future caller's seed is compatible.
There is no separate macro type system or type-checking pass. The
declaration-expansion availability rule is described below.

The author constructs the syntax returned by the step. For the example,
`next_number : Int -> (Int, Syntax.ExpressionFragment)` and `is_first` also
returns expression syntax. The first component remains the threaded state;
`from` provides the initial state, not a compiler input handle. The proposed
`SyntaxFragment<F>` conversion interface and its implementations are removed.
Conversion libraries are outside this slice.

Two authoring paths are intended:

1. Parse a syntax subtemplate, fill its variables, and return an expression
   fragment. This keeps a fixed shape close to ordinary Ash source. Check its
   syntax while compiling the source definition containing it, including an
   ordinary generator or helper, even when the function is never invoked.
2. Construct expression syntax procedurally with the syntax service. This
   permits a variable shape to be built from the generator state.

Both paths must return `Syntax.ExpressionFragment` and work with a step that
receives only its state. A final helper could have the ordinary type
`Int -> Syntax.ExpressionFragment`; intermediate helpers may use any ordinary
Ash types. Pure functions are expected. Where a function uses an effect row,
ordinary Ash checking and the existing compile-time host rules apply; macros
add no generator-specific effect rule.

Any ordinary Ash function with the required type can be used as the step.
The macro machinery threads its state and substitutes the fragment; it does not
inspect the function body or add a type checker. Reuse existing syntax admission
and diagnostics, and leave semantic checking to the ordinary compiler. I17
provides a subtemplate graph and a procedural graph that selects quote-created
fragments using the syntax service. It does not demonstrate fresh fragment
construction from raw syntax.

Check and execute the seed and step through the retained slice 1 host. Preserve
its checked entry, bounded execution, syntax services, authenticated handles,
result transfer and diagnostics. An internal Ash adapter with a monomorphic
`Input -> MacroResult` entry is one implementation candidate, not a required
representation. Caller-supplied seeds retain caller context; the step retains
its defining-module context. These rules add no macro-specific type checker.

An invocation-supplied seed may use an inline Ash expression, its own lexical
bindings and names from already checked imports. It cannot depend on the caller
module's own globals, whether written or generated: those declarations are not
available when declaration expansion runs. Report a staging diagnostic for
such a reference instead of silently substituting another binding. A seed
written in the macro definition may use that definition's already checked
helpers and dependencies, under slice 1's definition-site authority rules.
The compile-time entry and its dependency closure obey the existing checked-host
effect and execution bounds. Availability of caller-module globals may be
widened in a later proposal.

The step function is checked during its defining module's ordinary compilation.
The expander preserves source and context, threads state and substitutes values;
it does not inspect or independently check the function's type or body. The
existing checker handles generated uses and declarations, reporting incompatible
caller seeds or uses as ordinary Ash errors.
Syntactic admission remains responsible for complete fragments and their
placement.

At definition time, parse the template and check the macro notation's capture,
generator and repetition bindings. Do not resolve free template names then.
At invocation, resolve surviving names in their preserved definition context;
ordinary checking handles generated declarations and propagates their errors.
An unused template with an unresolved free name is valid, while an unused
syntactically malformed template is rejected by the parser. This follows the
retained expression slice; the accepted declaration-specific policy is not yet
implemented.

Declaration and derive macros have distinct entry forms. Expand them in source
order before ordinary module resolution. Each derive receives the original
subject and adds its output after that subject; it needs no semantic analysis
of the subject. For a deriving list, invoke all listed derives left to right,
then process their generated output in order, including nested expansion,
before proceeding to the next source declaration. Report the first expansion
failure in that order. The choice does not impose a separate module-wide derive
pass or constrain ordinary parser and downstream diagnostic scheduling. Expand
nested declaration invocations using their source syntax context and the
existing expansion limit. Collect complete output before resolving bodies, so
ordinary forward and mutually recursive references work. A failing invocation
publishes none of its output.
If a concrete use later requires derive output after identities or checked
summaries exist, define incremental admission and invalidation and show that
already checked opaque bodies are not reopened. Do not create that later
mechanism merely to share an API.

CP-0034 is accepted. An owning task and authorized delivery base are still
needed before product implementation. The programs below are acceptance inputs;
their connected execution remains outstanding.

## Integration corpus

The [I01–I21 integration manifest](fixtures/README.md) fixes the initial source
graphs, observable results and mutation assertions before product
implementation. I17 covers the additional generator scope; I18 covers the
syntax API contract already included in the original allocation.
Expected results and individual negative variants cannot be
relaxed as work proceeds; new cases may be added. All generated outputs cross
the real public compiler driver and ordinary checking. Runtime results use the
interpreter unless a case explicitly names another consumer. Human and JSON
diagnostics are asserted by structured cause and source role, not frozen
message wording. `forms.ash` denotes a separately imported macro module, because
CP-0033 forbids using a module's own syntax definitions.

The examples below use the candidate declaration invocation spelling and
ordinary Ash entry syntax. The linked fixture graph supplies the macro
definitions and complete entry files; their macro paths require implementation.

### I01–I07: every declaration form

| ID | Entry module after `import forms (syntax NAME)` | Ordinary expansion and observable result |
| --- | --- | --- |
| I01 | `make_type Color constructor Red`; `main () = match Red(42) { Red(value) => value }` | `pub type Color = Red(Int)`; result 42. A generic, multi-constructor variant and duplicate-name refusal are required. |
| I02 | `make_newtype Box constructor Box`; `main () = match Box(42) { Box(value) => value }` | `pub newtype Box = Box(Int)`; result 42. A generic and an opaque cross-module variant are required. |
| I03 | `make_interface Marker method mark`; a handwritten `impl Marker<Int>` returns true; main branches on `mark(0)`. | Generate `pub interface Marker<A> { mark : A -> Bool }`; result 42. Verify export, multiple methods and duplicate-method rejection. |
| I04 | Handwritten `interface Marker<A> { mark : A -> Bool }` and `type Color = Red`; `make_impl Marker for Color method mark`; main branches on `mark(Red)`. | Generate `impl Marker<Color> { mark _ = true }`; result 42. Check missing/conflicting impl and method-head errors. |
| I05 | `make_effect Ask operation ask`; `main` handles `Ask.ask`. | Generate `pub effect Ask { ask : Unit -> Int }`; check exported operation and malformed or duplicate operations without adding effect semantics. |
| I06 | `make_foreign Fixture symbol Make`; `main () = 42`. | Generate a library with profile `x86_64-unknown-linux-gnu` and `Make : Unit -> F.Address`, with `F` from the macro owner's builtin import; check declaration/publication and ordinary profile errors without calling native code. |
| I07 | `make_identity id for Int`; `make_inline same for Int`; `main () = id(same(42))`. | Generate one signature-plus-equation global and one inline global; result 42. Missing/mismatched equations and invalid parameter syntax reject. |

The following complete candidate file graphs fix the positive I01–I07 inputs.
Their spelling uses unimplemented candidate syntax; they have not been parsed
or executed. For each case place this `forms.ash` beside its `main.ash`:

```text
import @builtin.foreign as F

pub syntax declaration: (make_type) $T:ident constructor $C:ident => {
    pub type $T = $C(Int)
}

pub syntax declaration: (make_newtype) $T:ident constructor $C:ident => {
    pub newtype $T = $C(Int)
}

pub syntax declaration: (make_interface) $T:ident method $m:ident => {
    pub interface $T<A> {
        $m : A -> Bool
    }
}

pub syntax declaration: (make_impl) $I:ident for $T:ident method $m:ident => {
    impl $I<$T> {
        $m _ = true
    }
}

pub syntax declaration: (make_effect) $E:ident operation $op:ident => {
    pub effect $E {
        $op : Unit -> Int
    }
}

pub syntax declaration: (make_foreign) $L:ident symbol $S:ident => {
    pub foreign library $L {
        profile "x86_64-unknown-linux-gnu"
        symbol $S : Unit -> F.Address { name "fixture_make" }
    }
}

pub syntax declaration: (make_identity) $name:ident for $T:type => {
    pub $name : $T -> $T
    $name value = value
}

pub syntax declaration: (make_inline) $name:ident for $T:type => {
    pub fn $name(value: $T) -> $T {
        value
    }
}
```

I01 `main.ash`, expected result 42:

```text
import forms (syntax make_type)

make_type Color constructor Red

main : Unit -> Int
main () = match Red(42) {
    Red(value) => value
}
```

I02 `main.ash`, expected result 42:

```text
import forms (syntax make_newtype)

make_newtype Box constructor Box

main : Unit -> Int
main () = match Box(42) {
    Box(value) => value
}
```

I03 `main.ash`, expected result 42:

```text
import forms (syntax make_interface)

make_interface Marker method mark

impl Marker<Int> {
    mark _ = true
}

main : Unit -> Int
main () = match mark(0) {
    true => 42
    false => 0
}
```

I04 `main.ash`, expected result 42:

```text
import forms (syntax make_impl)

interface Marker<A> {
    mark : A -> Bool
}

type Color = Red

make_impl Marker for Color method mark

main : Unit -> Int
main () = match mark(Red) {
    true => 42
    false => 0
}
```

I05 `main.ash`, expected result 42:

```text
import forms (syntax make_effect)

make_effect Ask operation ask

main : Unit -> Int
main () = handle (perform Ask.ask ()) with Ask {
    ask _ => resume 42
}
```

I06 `main.ash`, expected result 42; the foreign symbol is not invoked:

```text
import forms (syntax make_foreign)

make_foreign Fixture symbol Make

main : Unit -> Int
main () = 42
```

I07 `main.ash`, expected result 42:

```text
import forms (syntax make_identity, syntax make_inline)

make_identity id for Int
make_inline same for Int

main : Unit -> Int
main () = id(same(42))
```

The [I01–I07 fixture graph](fixtures/declarations/README.md) retains these
source files, basic negative variants and handwritten controls. The seven
controls returned 42 with the in-progress expression-slice compiler. The macro
graphs are not yet executable. The fixture README also identifies generic,
opacity and malformed-member graphs and their handwritten controls.

### I08–I21: connected behavior and negative cases

| ID | Fixed input and assertion |
| --- | --- |
| I08: form matrix | Invoke each form in I01–I07 and compare generated declarations and expected rejection categories with handwritten controls. Include visibility, generic parameters, repeated members, punctuation and malformed output. |
| I09: fixed derive | A `Color` type with `Red` and `Blue` constructors and a deriving clause is retained once; an interface-specific derive emits a `Marker<Color>` implementation. Main observes both constructors and returns 42. Include a `newtype` and a clause naming multiple derives; reject a deriving clause on an unsupported declaration form. |
| I10: structural derive | A derive on `Color` traverses its `Red` and `Blue` constructors and emits an implementation with distinct constructor match arms; both execute their expected paths. A payload-bearing or unsupported constructor shape returns the specified authored diagnostic. |
| I11: variable size and procedural parity | Run the same derive on one, two and at least three constructors; compare handwritten target behavior with a real checked Ash transformer. If declarative repetition is selected, run the equivalent declarative derive and compare binding and outputs. |
| I12: caller/module hygiene | Generate public globals and nominals/constructors with caller-selected and macro-written names; later caller declarations and an importing module use them by spelling. Generated private or public name conflicts reject in ordinary downstream checking, with both sources and macro origins identified. Caller-selected distinct helper and type names succeed; import collisions reject. |
| I13: owner authority | An imported macro references its private helper and a renamed/qualified public dependency despite caller shadowing. The caller cannot directly access the helper or a dependency's opaque constructor. Include a facade import. |
| I14: output and staging failures | Reject imports, syntax definitions, malformed declarations, recovery nodes, partial declarations and out-of-category protected fragments. Preserve the original module graph and publish no part of a failed expansion. Reject malformed unused templates at definition time; check generated-program errors through ordinary Ash checking. |
| I15: diagnostics and limits | Reject a generated type error, missing name, author rejection, invalid output and bounded recursion. Human and JSON output retain distinct causes, invocation, definition and relevant original input; repeated compilation preserves observable output modulo fresh identities. |
| I16: real graph and consumers | A macro library, its helper dependency, a caller with a derive and declaration macro, and an importer of generated public names compile and execute through the public driver. Exercise interpreted and supported build/image execution, host root teardown, authenticated input handles and independent Core validation. Test source access and opacity with ordinary resolver and linker rules. |
| I17: generator-assisted template | With the two-generator `make_constants` example above, construct syntax fragments explicitly and observe results 100, 1 and 2 in source order. Compare a template-level generator's `0, 1, 2, 3` with a generator attached to the outer repetition's `0, 1, 0, 1`. Use a step returning `Syntax.ExpressionFragment` and checked execution on the public path; repeated use within an iteration; independent seeds; rejection of duplicate generator names; inline and imported invocation-supplied seeds; rejection of a caller-module global seed; a seed fixed in `with`; a generator with an invalid return type; generated code with a type error; an invalid fragment category; checked execution and bound failures; and no partially published declarations. |
| I18: closed-sum migration | For a public syntax sum actually extended by the proposal, check that an old exhaustive match without a fallback is rejected for its missing new cases. Update the consumer to handle the new cases and show that its existing expression transformation still works. Check an existing fallback only where its behavior is correct, and preserve syntax origins and contexts across the migrated transformer. |
| I19: repetition and captures | Match zero, one and multiple items with `*`, and one and multiple with `+`; reject zero with `+`. Exercise separators, paired equal-length captures in source order, a length mismatch, and each supported identifier, type, expression, pattern and braced multi-line declaration capture. |
| I20: nested declarations | Generate an invocation of another declaration macro and verify source-order output and definition-versus-caller syntax context. Exercise forward and mutually recursive references, a bounded recursive expansion failure and atomic rejection without partial publication. With two authored expansion failures, verify that a derive preceding a declaration invocation fails first, and vice versa. |
| I21: contextual declaration | Define `syntax declaration: (name)` in a macro module; separately use `declaration` as an ordinary identifier and as a CP-0033 expression-syntax name with `:` and identifier matcher literals. Verify unchanged parsing and behavior. Check imported syntax-name collision and rename rules and reject a module's use of its own syntax definition. |
| I22: executable escapes | Exercise all five capture kinds as syntax values, nested quotes and escapes, repetition drivers and cached generators, ordinary helper calls, syntax contexts and origins, zero iterations, atomic failure, ordinary type errors and the reserved `syntax` word. The [escape graphs](fixtures/escapes/README.md) specify the source inputs and assertions. |

The fixed-derive case I09 has these candidate inputs. The derive receives the
type declaration itself; there is no separate caller-supplied target name.
Its declarative definition follows the approved working derive authoring
design accepted in CP-0034.

`api.ash`:

```text
pub interface Marker<A> {
    mark : A -> Bool
}
```

`derives.ash`:

```text
import api (Marker, mark)

pub syntax derive: (marker) $target:ident => {
    impl Marker<$target> {
        mark _ = true
    }
}
```

`main.ash`, expected result 42:

```text
import api (Marker, mark)
import derives (syntax marker)

type Color = Red
    | Blue
    deriving (marker)

main : Unit -> Int
main () = match (mark(Red), mark(Blue)) {
    (true, true) => 42
    _ => 0
}
```

The negative variants must be defined once the derive API and clause grammar
are selected. The example is a proposal, not a complete executable contract.

I10 fixes the following ordinary target. A structural derive accepts the
complete `Color` declaration and emits the two method equations in source
constructor order. Its two paths are observed by `main`:

```text
interface Indexed<A> {
    index : A -> Int
}

type Color = Red
    | Blue

impl Indexed<Color> {
    index Red = 1
    index Blue = 1
}

main : Unit -> Int
main () = index(Red) + index(Blue) + 40
```

The candidate input replaces the type and impl above with the following
derive; the interface is imported from a separate `api.ash`, and the derive
is imported from a separate checked syntax module:

```text
type Color = Red
    | Blue
    deriving (indexed)
```

The handwritten target and generated program must both return 42. The
one-constructor I11 variant emits one equation; the three-constructor variant
emits three and observes each at least once. The payload-bearing variant
with `Red(Int)` and `Blue` on separate constructor lines is rejected by this
particular derive with an authored unsupported-shape diagnostic at `Red(Int)`.
This rejection is a
property of the sample derive, not a restriction on declaration macros.
The complete proposed [I10/I11 fixture graph](fixtures/indexed/README.md)
contains the interface, checked Ash transformer, callers and payload rejection.
Its ordinary Ash bodies have been checked against a temporary stand-in for the
new syntax-service declarations; the macro-specific path is not implemented or
claimed to pass.

The proposed [I12/I13/I16 module graph](fixtures/hygiene/README.md) fixes a
declaration/derive integration case, caller shadowing, definition-private
helpers, a renamed facade route and negative variants. The proposed
[I17 generator graph](fixtures/generators/README.md) fixes concrete inline,
imported and unavailable caller-global seeds, as well as nested generator
initialization. These graphs are proposed inputs, not passing tests.

The [I21 header compatibility graph](fixtures/header_compat/README.md) fixes
the formerly ambiguous expression header and the parenthesized declaration
header. Its expression-only control returns 42 in the in-progress slice 1
compiler; the combined graph awaits slice 2.

The [I14/I15 diagnostic graphs](fixtures/diagnostics/README.md) fix source and
expected causes for a generated type error, missing capture, unused malformed
template, forbidden import and bounded recursive expansion. Their transformer
body has been checked separately; the proposed declaration path has not run.

The [I19 capture and repetition graphs](fixtures/captures/README.md) fix source
for expression, pattern and complete declaration captures, empty `*`, nonempty
`+`, and unequal repetition drivers. Their handwritten control returned 128;
the macro graphs have not run.

The [I18 closed-sum migration graphs](fixtures/migration/README.md) preserve
the original exhaustive consumer and its explicit six-case migration. The old
expression macro returned 42 under the in-progress slice 1 compiler; the new
sum and migration graph require slice 2.

The [I09 deriving-clause graphs](fixtures/derives/README.md) fix multiple
derives, a newtype, renamed imports, generated subjects and the principal
clause failures. Their handwritten control returned 42; the derive graphs
require slice 2.

The [I20 nested declaration graph](fixtures/nested/README.md) fixes lookup of a
macro emitted from definition context in the presence of a conflicting caller
syntax import. Its ordinary control returned 42; nested expansion awaits
slice 2.

The manifest and fixture READMEs fix the starting files, import graphs, negative
variants and expected outcomes. Review must check their coverage against the
catalogue. Implementation must supply the mutation harness and run the graphs
through the proposed production path; the handwritten and stand-in controls do
not establish that the macro implementation works.

## Prospective tasks and gates

Each row is one proposed work unit, not an active task. Points allocate the
fixed functionality total once. Evidence rows identify mandatory integration
cases; each unit also requires focused positive/negative checks and review of
its actual changed boundary. No unit earns full acceptance from a helper-only
test when its gate requires the production driver. The eventual owning task
must pin exact files, receipts, owners and final full-gate checkpoints.

Each unit is at most four points. The original units below subdivide the
65-point prediction; incremental units separately account for the added
30-point scope. Gates identify the assertions owned by each unit;
where a full integration case needs later producers, its early parsing or
admission checks can run first, but the unit's integration assertion remains
pending until the connected driver path is available.

| ID | Work | Points | Prerequisites | Acceptance gate |
| --- | --- | ---: | --- | --- |
| D01a | Parse declaration-syntax headers, retain templates and select imports | 2 | Retained CP-0033 and accepted CP-0034 | I01/I07 header and import selection; I14 malformed headers; ordinary syntax compatibility. Complete template admission belongs to D02a/D03. |
| D01b | Parse declaration invocations and their matcher captures | 3 | D01a | I01/I07 invocation and fragment boundaries through the driver; I14 missing or malformed capture. |
| D02a | Parse ordered declaration output and retain fragment metadata | 3 | D01b | I01/I02/I07 output order and category projection, followed by their connected driver assertions. |
| D02b | Admit complete output atomically and reject invalid categories | 2 | D02a; H01a staging | I14 partial, recovery-bearing and forbidden output rejection with no partial publication. |
| D03 | Connect ordinary declaration parsing and projection for output forms | 4 | D02a/D02b | I03–I08 through the ordinary parser, including foreign declarations and negative controls; no per-form macro semantic checker. |
| R01a | Parse one deriving clause and capture its type or newtype subject | 2 | D01a/D02a | I09 one subject and derive selection; malformed clauses and unsupported-subject refusals. |
| R01b | Retain the derive subject exactly once and append one derive's output | 3 | R01a; H01b derive entry | I09 one subject/output order; I14 failed-derive atomicity. |
| R02a | Author the example derive's syntax traversal | 3 | R01b/P01/R05 | I10/I11 one and multiple constructors preserve names, order and origins; the authored derive rejects unsupported shapes. No compiler semantic inspection. |
| R02b | Author and connect variable-length derive output | 4 | R02a/P02 | I10/I11 one-, two- and three-constructor implementations execute and agree with handwritten controls and required output order. |
| P01 | Checked Ash declaration/derive input, handles and structural API | 3 | D02a; syntax API agreement | I11 input, I14 handle/category refusals and I18 closed-sum migration. |
| P02 | Checked Ash declaration output, transfer and host lifecycle | 4 | P01/D02a | I11/I16 real transformer, teardown, invalid output and no partial result. |
| H01a | Stage declaration expansion and allocate resulting module identities | 3 | D02a | I01/I12/I16 declaration entry, output order and forward references through the driver. |
| H01b | Expand derive entry forms and merge output in source order | 3 | H01a/R01a | I09/I12/I14/I20 derive timing, retained subject, forward references and source-ordered expansion failures. |
| H02a | Preserve caller-selected and introduced term binders | 3 | H01a | I07/I12 generated globals: caller-selected distinct helper names and ordinary duplicate-name diagnostics. |
| H02b | Preserve caller-selected and introduced non-term binders | 3 | H01a | I01/I02/I03/I04/I12 type, constructor, interface and method contexts with captured-versus-introduced refusals. |
| H03a | Preserve definition-context public imports and aliases | 3 | H01a/H02a; retained CP-0033 contexts | I13 qualified, renamed and facade routes retain identity under caller shadowing. |
| H03b | Resolve definition-private references and retain checked closure | 2 | H03a | I13/I16 private helper survives linking; ordinary resolution rejects direct caller access and inaccessible opaque members. No per-reference grant objects. |
| H04 | Connect generated declarations to ordinary publication | 3 | H01a/H02a/H02b | I03/I04/I12/I16 importer visibility, ordinary duplicate names and impls, and opaque controls. |
| V01a | Report malformed expansion and transformer failures | 3 | D02b/R01b/P02; common origin interface | I14/I15 invalid output, authored rejection and bounded failure retain causes and locations in human and JSON. |
| V01b | Report ordinary generated-program failures with multiple origins | 2 | D02a/H02a; common origin interface | I15 generated type/name errors retain input, invocation and definition causes in human and JSON. |
| V02 | End-to-end graph, runtime/build consumers and validation | 4 | D03/R02b/P02/H03b/H04/V01a/V01b | I08–I16 and handwritten comparisons; public driver, supported image and Core mutation controls. |
| V03 | Final specification audit, integrated QA/review and retained gate | 3 | All preceding units and incremental units below | Complete I01–I21, documentation/link/authority checks, review repairs, fresh required workspace gate and acceptance record. Earlier QA and reviews proceed per unit. |
| **Original subtotal** | | **65** | | |

The D units sum to 14, R units to 12, P units to 7, H units to 20, and V units
to 12. Each point belongs to one row; an integration graph may support several
rows only through separately identified assertions.

The following units are the 30-point estimate for scope added after that
prediction. They are not earned credit and do not change the original points.
The named assertions are parts of the same integration corpus, not replacement
tests. A task can start when its producer/consumer interface and prerequisites
are agreed; its acceptance still requires its stated connected evidence.

| ID | Incremental work | Points | Prerequisites | Acceptance gate |
| --- | --- | ---: | --- | --- |
| G01 | Parse matcher/template repetition and trailing generator clauses | 3 | D01a/D01b; grammar agreement | I17/I19 nested repetitions, clause ownership, malformed binding and separator refusals. |
| G02 | Bind unique generator names and their lexical scopes | 3 | G01 | I17 duplicate-name refusal, independent names and references confined to their owning template. |
| G03 | Check and evaluate seed expressions in the compile-time environment | 4 | G02/P01; compile-time call interface | I17 inline and imported seeds execute; caller-global and wrong-type seeds reject at their source. |
| G04 | Construct ordinary step calls and preserve syntax fragment contexts | 4 | G02/P01/P02; compile-time call interface | I17 checked fragment-returning step, wrong return type, fragment admission and source origins. |
| G05 | Execute per-scope generator state and iteration caching | 4 | G03/G04 | I17 `0,1,2,3` versus `0,1,0,1`, repeated splices, empty iterations and independent states. |
| G06 | Preserve generator errors, origins and atomic failure | 3 | G03/G04/V01a/V01b | I15/I17 checked-step, bound and generated-code failures retain causes and publish no partial result. |
| G07 | Run generator integration and generator-specific review | 2 | G05/G06; connected driver | I17 complete public-driver graphs, source and structured diagnostics, focused review and repairs. |
| R03 | Disambiguate deriving clauses at type boundaries | 2 | R01a; retained CP-0033 parser | I09/I21 clause precedence, syntax rename and unchanged expression-syntax controls. |
| R04 | Expand ordered multiple derives and generated deriving subjects | 3 | R01b/H01b/R03 | I09 multiple derives retain one original subject, preserve order and fail atomically; nested output is bounded. |
| R05 | Bind the subject name in declarative and procedural derives | 2 | R01a/P01; capture-order contract | I09/I10 subject and identifier captures retain source origin and caller context; missing optional binding is reported. |
| **Incremental subtotal** | | **30** | | |
| **Revised total** | | **95** | | |

### Order and parallel work

First agree the declaration-fragment, derive-capture, hygiene and diagnostic
interfaces and define the complete fixture source. D01a, D01b, D02a and H01a
establish the first connected declaration path. D02b depends on H01a's staging;
R01a can proceed after D02a, and H01b supplies the derive entry needed by
R01b. P01 can proceed after D02a and the syntax API agreement; P02 and R02a
depend on their stated producers, and R02b combines traversal and output.

After H01a establishes the shared scope policy, H02a and H02b have distinct
term and non-term acceptance cases. H03a follows the term context and H03b
adds private closure; H04 follows both binder units. D03, the derive path,
the procedural path and the scope paths are candidates for parallel work once
their producer/consumer contracts are agreed, subject to their stated
dependencies. V01a and V01b can be designed in parallel once origin producers
and consumers are agreed, but their gates depend on completed producers. V02
and V03 integrate the full path after their prerequisites.

G01 and R03 have separate grammar surfaces and can proceed in parallel once
their shared token and parser interfaces are agreed. G02 follows G01; G03 and
G04 can proceed in parallel after G02 and their host interfaces are available.
G05 joins the two paths, while G06 can proceed when its error producers are
available; G07 checks their connected result. R05 follows R01a and P01 and
supplies the captured-name contract used by R02a. R04 adds multiple and nested
derives after the single-derive and clause-entry paths. These units may overlap
with other work only at the agreed interfaces; V03 follows all of them.

A prerequisite permits the consumer to start once the named producer's
agreed interface and focused checks are available. It does not require
prematurely marking that producer accepted: its production-driver assertion
may need the consumer, and remains pending until the shared vertical path runs.

Development, design, planning, QA and review can run concurrently on
different work units. An individual unit still follows its own dependencies:
its design and input/output contract must be ready for implementation; QA and
review assess a specified candidate; acceptance requires that unit's gates.
There is no milestone-wide pause in development while another unit is being
designed, tested or reviewed. V03 owns the final integrated audit; it does not
defer all QA or review until the end.

Assignments name the scope, producer/consumer interface, artifact and owner,
and must not duplicate or conflict with another active assignment. A reviewer
may independently inspect a developer's same pinned result; independent review
and QA have distinct responsibilities even when they examine the same result.
For example, while a developer implements D01b, a planner can specify R01a's
derive input, QA can prepare or verify D01a cases, and the reviewer can inspect
an immutable D01a candidate or challenge R01a's proposed boundary. Each action
uses the dependencies and inputs it actually needs.

Schedule access to shared checkouts, files, build caches and heavy tools so
concurrent assignments cannot overwrite one another or change a frozen
verification input. Follow the then-current Ash workflow, assign one integration
owner, and serialize shared product writers and heavy builds as required.
Review and QA identify their exact candidate; if it changes, refresh the
affected assessment before counting its gate. The integration owner checks
the combined production path after the independently progressing units connect.

## Before implementation

1. Use the recalibrated [local plan](slice2-delivery-plan.md) for the accepted
   scope. C3 reviewed the public-name contract and corpus; connected public-name
   behavior remains an implementation gate. The generator's ordinary function
   type is decided; no conversion interface or separate evidence mechanism is
   required. Preserve the earlier predictions.
2. Establish an owning task and authorized delivery base. Product
   implementation, its mutation harness and passing integration evidence
   remain outstanding.
