# DN-0062: Hygienic Surface Macros

- ID: `DN-0062`
- Status: exploring
- Related: [AD-0001](../decisions/AD-0001-implementation-environment.md),
  [AD-0005](../decisions/AD-0005-parser-architecture.md),
  [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md),
  [DN-0030](DN-0030-typed-compiler-macros-and-hooks.md),
  [DN-0061](DN-0061-effects-and-resources-first-slice.md)

> This draft is informative. It does not define current Ash, accept a language
> change or architecture, or authorize implementation. All macro syntax and
> diagnostic text below are illustrations, not selected grammar or wording.

## Question

Can Ash libraries define convenient surface syntax with declarative and
procedural transformations while preserving lexical binding and descriptive
errors? What can such transformations express using current or proposed Ash,
and where do effects and other features require later typed elaboration or
additional checked language mechanisms?

The larger goal is a small semantic Core and a small set of general checking
and inference rules. Ash-authored syntax and typed elaboration would express
features through those shared mechanisms where their contracts permit it. A
program should require only the compiler services and rules needed by its
syntax, dependencies, inferred contracts and generated code, plus a shared
foundation. Reducing total compiler and library code is an aspiration, not
the primary measure of success.

The immediate motivation is the effects work. Some wrappers, declarations,
and notational forms may be expressible as syntax expansion over a smaller
set of operations. The amount of compiler work that can move to libraries is
not yet established. Compare actual transformations and their obligations
before identifying a smaller language nucleus.

## Context and boundaries

The [current specification](../../spec/README.md) defines effects, requests,
lexical handlers, one-shot continuation use, scoped resources and cleanup. It
does not define macros. Current effect and resource rules continue to apply to
any future expanded program unless a separate language change replaces them.
A macro cannot establish a missing runtime operation or prove an ownership,
completion, or continuation property merely by generating syntax.

The accepted, unimplemented [effects-to-interfaces elaboration package](effects-resources/effect-interface-elaboration-proposal.md)
keeps effect syntax while translating effectful functions, requests and handlers
through typed contracts and generated continuations. It changes handler-context
behavior and carries an explicit one-shot verification gap; neither the
translation nor that proposed change is current Ash. Its treatment of rows,
handler boundaries and whole-function conversion challenges the assumption
that a local, untyped surface rewrite is sufficient. Compare it separately with
surface convenience forms and with later typed transformations. Do not infer
that macros can replace the package without evidence for its complete contract.

[DN-0030](DN-0030-typed-compiler-macros-and-hooks.md) explores transformations
at typed compiler boundaries, registration and selection. Those questions are
related but distinct from a user explicitly invoking a surface syntax form.
A typed transformation may depend on resolved identities, inferred rows or
other facts unavailable to an early syntax transformer. It also has its own
validation and semantic-preservation obligations.

The current [syntax](../../spec/syntax.md) uses structured expressions,
patterns, declarations and logical line boundaries, rather than S-expressions.
Names currently resolve to stable identities before typing, with distinct
term, type and other scope rules; see [name resolution](../../spec/name-resolution.md#local-scope)
and [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md). In
particular, block bindings are sequential, recursive groups are simultaneous,
and handler clauses carry a hidden continuation capability.

[AD-0005](../decisions/AD-0005-parser-architecture.md) selects a closed parser
assembly and a token-complete concrete representation projected to a validated
surface AST. A library-defined syntax form can require a change to this boundary,
including parsing, error recovery and tooling. [AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md)
requires structured reasons and causal spans; [AD-0007](../decisions/AD-0007-typed-core-dialects.md)
requires Core provenance and independent validation. Neither decision selects
a macro model.

## Working direction

Compare a single binding-aware syntax representation with two authoring forms:

- Declarative patterns and templates for local, syntax-directed expansion.
- Procedural transformers for computations that inspect and construct syntax.

Both would use the same expansion and hygiene rules. This is a working
preference, not a decision. It avoids requiring two independent accounts of
binding, but a token-oriented interface or a smaller initial rules-only system
may prove preferable. Surface macros and typed compiler transformations need
not use the same public representation.

### General rules and program-specific work

Compare candidates by the semantic Core forms and checking rules they require,
not just by the surface spellings they remove. A rewrite is a simplification
only when the target forms and general rules establish the original behavior
and obligations. For example, a general function-and-match account could serve
both equational and operational presentations. It must still check argument
grouping, patterns, coverage, scope, types and effects.

For effects and resources, the intended destination is general rules for the
facts that computations establish and compose, including control use,
ownership and completion. Ash code could construct and compose the associated
terms and contracts through compiler interfaces. The checker must establish
their premises; a syntactic wrapper or a general-looking function call does
not supply a missing ownership or one-shot guarantee. Trace each existing
check to a replacement, a retained boundary or a remaining obligation. The
first-slice work in [DN-0061](DN-0061-effects-and-resources-first-slice.md)
owns the corresponding rule development; this note does not preselect its
answer or waive [AD-0007](../decisions/AD-0007-typed-core-dialects.md)'s
independent validation of transformed Core.

Distinguish the implementation present in a compiler artifact, the components
loaded or initialized for one compilation, and the rules and analyses actually
run. An Ash module holding an elaborator does not by itself reduce all three.
Record feature dependencies through source syntax, macros, imports, generated
code, inferred contracts and checking obligations. In particular, an imported
function can carry an effect requirement without a local `perform`, and
ordinary construction has the current default allocation requirement. Avoid
assuming that a source program with no explicit resource syntax requires no
storage-related semantics. Dependency discovery and any fixed-point policy
remain open.

### Ash-defined compiler interfaces

The working direction is to define the exposed compiler concepts and
transformation interfaces in Ash modules, independently of Rust data layouts.
The current Rust compiler can adapt its internal structures to those contracts;
a future Ash compiler may use the same types directly or provide its own
adapters. Only the compiler representations deliberately exposed at a phase
need such an interface. Backend types and internal caches do not become part
of it merely because a compiler uses them.

Compiler-provided operations or authenticated identities may need a small
`@builtin` boundary. Under this direction, builtin means a facility supplied
according to an Ash contract, not a Rust object exposed as language truth.
Whether the contracts are ordinary Ash modules, compiler-owned declarations,
or a combination remains a design question. Current Ash has no macro bridge
or compile-time transformer invocation. [AD-0001](../decisions/AD-0001-implementation-environment.md)
selects Rust for the current implementation; it does not establish a
self-hosted compiler or browser execution.

The boundary must transfer syntax categories, binding contexts, authenticated
identities and causal origins in both directions. A compiler-to-Ash-to-compiler
round trip of unchanged syntax must retain its relevant structure, binding
relationships and provenance. Constructed results must distinguish preserved
and introduced context, enforce access and opacity, and undergo the applicable
checking. Representation choices, lifetime, sharing, separate compilation,
versioning and failure remain open; the contract need not mirror every
implementation type or promise an unrestricted inverse conversion.

Browser execution adds two distinct targets. A native-hosted compiler could
expand macros before producing a WebAssembly program; alternatively, a
browser-hosted compiler could execute macros there while compiling. The shared
Ash interfaces should not depend on which compiler language or host is used.
Each route still needs its own execution, host-service, effect, resource and
completion support. This note does not select a WebAssembly backend or claim
browser support.

### Natural syntax

A syntax extension should be able to express a form such as:

```text
if ready then start () else wait ()
```

One illustrative declarative definition is:

```text
syntax if $condition:expr then $yes:expr else $no:expr => {
    match $condition {
        true => $yes
        false => $no
    }
}
```

Literal words delimit captured expressions. The resulting `match` evaluates
its condition once and evaluates only the selected branch. The notation does
not decide how macro definitions are written, imported or parsed. In
particular, `if`, `then` and `else` are valid identifier spellings in current
Ash; a future design must account for existing uses.

The expander must recognize the form before the whole expression can be parsed
as current Ash. One candidate registers a distinctive leading keyword and a
pattern with literal separators. Another requires explicitly delimited uses,
such as `if!(condition, yes, no)`. The latter bounds parsing and conflicts but
cannot provide the same unmarked syntax. A third permits more general grammar
extensions, with larger ambiguity, tooling and compatibility costs.

For natural syntax, determine how nested forms associate, how expression
captures terminate, and how the form interacts with juxtaposed application,
infix precedence, line boundaries and parentheses. A pattern must not consume
an inner `else` as an outer separator. Determine how ambiguities, overlapping
forms, imports, shadowing and local syntax scopes are reported. Contextual
keywords, reserved keywords and an explicit namespace are alternatives, not
accepted choices. A library-defined syntax environment may require revising
AD-0005's closed assembly; it must not silently bypass that decision.

### Declarative patterns

A rules system could match literal tokens and delimited groups, capture parsed
fragments such as expressions and patterns, and substitute them into templates.
Repetition and separators may be useful for effect operations, handler clauses
and declarations. The admissible fragments and output categories need explicit
boundaries: an expression expansion, for example, must result in an expression.
A matcher must define fragment termination and reject ambiguous repetition.
Literal keywords and literal identifiers may need different matching rules;
if identifiers match by binding, aliases and shadowing need examples.

An illustrative expression macro introduces a temporary:

```text
macro first_or {
    ($first:expr, $fallback:expr) => {
        let temp = $first
        match temp {
            true => true
            false => $fallback
        }
    }
}
```

For `let temp = true` followed by `first_or!(false, temp)`, the fallback
must refer to the caller's `temp`, not the generated temporary. The result is
`true`. The first argument is evaluated once; the fallback is evaluated only
when the first is false. Binding hygiene does not itself ensure either
execution property; they follow from this particular template and the checked
semantics of its expansion.

### Procedural transformers

A procedural transformer receives syntax, uses compile-time computation to
inspect or assemble it, and returns syntax for an allowed output category.
Quotation, splicing and pattern matching can use the same syntax objects as
declarative rules. For example, a transformer for `all!(a, b, c)` can fold a
list of captured expressions into nested `match` expressions, evaluating each
in order and stopping at the first false value. Declarative recursion might
also express this example; it does not establish a need for procedures.

More demanding comparisons include checking relationships among repeated
inputs, producing related declarations and reporting a specific invalid
combination. The result must pass the ordinary parsing or structure validation,
resolution, typing and elaboration applicable to its category. Generated Core,
if a later interface can produce it, still crosses AD-0007's independent
validation boundary.

Whether transformers are written in Ash, how compile-time code is built and
executed, its allowed effects, resource limits, dependency tracking and build
inputs remain open. Imports of transformer code and its compile-time
prerequisites must not silently create module cycles or ambient execution.
Describe nontermination and failure as compiler diagnostics or build behavior
only after selecting an execution model.

### Comparison with Scheme and Rust

Scheme's [syntax-rules and syntax-case](https://www.scheme.com/tspl4/syntax.html)
show declarative and procedural transformations with binding-aware syntax.
Their use of S-expressions is not a requirement for lexical context, patterns
or templates. Ash must nevertheless solve its own expression boundaries and
precedence.

Rust's [macros by example](https://doc.rust-lang.org/reference/macros-by-example.html)
show delimited patterns, fragment categories and repetitions in a non-S-expression
language. They use mixed-site hygiene. Rust's [procedural macro interface](https://doc.rust-lang.org/reference/procedural-macros.html)
consumes and produces token streams, not the compiler's AST, and its reference
describes procedural macros as unhygienic. Libraries can parse those tokens
into their own structured representations. A binding-aware Ash interface could
instead retain lexical context through syntax operations, at the cost of
specifying and maintaining that interface. A hybrid could preserve delimited
tokens while exposing parsed syntax fragments; compare its context and
compatibility guarantees explicitly.

## Hygiene and binding

A hygienic default should preserve caller bindings in supplied syntax, keep
macro-introduced temporaries distinct from caller bindings, and resolve free
references introduced by a template in the macro's definition context. A
fresh spelling or gensym alone does not solve definition-site references,
imports, nested macros or explicit caller-supplied binders.

Syntax objects can carry lexical context alongside spelling and provenance.
The [scope-set model](https://docs.racket-lang.org/reference/syntax-model.html)
is one candidate: lexical binding and expansion introduce scopes; resolution
uses the identifier's context to identify the appropriate binding. Ash must
establish its own precise rules and ambiguity behavior rather than assume the
model transfers unchanged. Lexical context and source provenance are distinct:
retaining one does not imply retaining the other.

A binding form must extend the correct syntax regions. A `let` initializer
sees the preceding scope, whereas its binder scopes over the later block
remainder. A recursive group has different scope. Pattern binders enter
together; local nominal and constructor names, type parameters, region
identities, imports, aliases and shadowing also need their existing policies
preserved. Macro-generated declarations raise separate questions about
visibility, exports, duplicate names and references to private definition-site
helpers across module boundaries.

A macro may intentionally take a caller-written binder and bind a caller-written
body, for example a hypothetical `with_value!(name = value, body)`. That use
must bind the supplied name in the supplied body without allowing an unrelated
macro-generated name to capture caller references. The expander must account
for the binding form's actual scope, not merely tag every generated identifier
alike. Explicit context-manipulation operations, analogous to Scheme's
`datum->syntax`, could support intentional introduction of a caller-visible
name. Their guarantees and risks require separate examples; ordinary templates
and splices should not silently change context.

`resume`, `discard` and `retain` refer to clause capabilities under current
rules, rather than ordinary named variables. Hygiene for identifiers alone
does not define whether a macro-generated use is admitted, which clause owns
it, or how nested handlers affect it. Those cases must pass the applicable
control checks and receive their own expansion and diagnostics tests.

## Macro-writing tactics for names and bindings

These tactics are candidates for an author-facing model, not operations that
Ash currently supplies. The examples use schematic macro syntax. A complete
model needs positive and negative cases for every name category below, including
imports, shadowing and nested expansions.

### Keep a definition-site reference

A macro can need a function defined in its own module or imported there. Under
the working hygienic model, a literal free reference in its template retains
the macro definition's context. Calling that function is an ordinary use of
hygiene; it does not require capture or a hygiene escape.

For example, a module defining a macro could contain:

```text
import @builtin.integer as Integer
import @builtin.string (byte_length as size)

normalize : Int -> Int
normalize value = value

macro split_normalized {
    ($value:expr) => {
        Integer.split_base256 (normalize $value)
    }
}

macro string_size {
    ($value:expr) => {
        size $value
    }
}
```

If another module invokes these macros, `normalize` denotes the macro module's
function, `Integer.split_base256` denotes the function selected by its complete
import, and `size` denotes the targeted import's original function. A caller's
local `normalize` or `size`, or its own distinct module alias `Integer`, must
not redirect those template references. A caller-supplied `$value` still resolves
in the caller's context. The identifier `Integer` in a qualified reference is
a module alias in a distinct syntactic role; its member must be resolved through
the correct module, not looked up independently by spelling.

This is the intended behavior to test, not a claim that Ash already permits
exporting macros or accessing a defining module's private functions through
them. Definition-site reference preservation needs a separate policy for
private helpers, dependency edges, checked exports, retained executable
artifacts and separate compilation. Identity alone is not authorization. A
future design could allow an exported macro to retain an authenticated private
helper reference, require a public helper, or use another explicit mechanism;
compare the costs and access rules before choosing. None permits arbitrary
source access to unrelated private declarations or opaque constructors.

The same concern applies to types, constructors, interfaces, methods, effects
and operations. Definition-site identity for a method or function also does
not by itself select an interface implementation or an effect handler. Current
imports have a separate implementation-fact channel, and handlers have dynamic
and lexical rules. Define which evidence is available to generated code rather
than assuming that preserving a name captures all of its surrounding context.

### Keep caller syntax and caller-selected names

Splice a caller-supplied expression, type, pattern or identifier without
reconstructing it from its spelling. Its references retain the caller's lexical
context. When the caller explicitly supplies a function name or qualified
reference as an input, generated use of that input should refer to the supplied
binding, including a targeted import or alias selected by the caller. This
allows the caller to choose behavior without unhygienic lookup.

A transformer must distinguish preserving a caller's reference from creating a
new identifier with the same text. A source fragment may contain nested syntax,
shadowing and references from several scopes. Replacing the fragment with its
printed text and reparsing it cannot be assumed to retain any of these facts.

### Introduce private names and explicit binders

A template may introduce a temporary and its references under a fresh expansion
context. Each invocation must receive distinct generated bindings, while uses
of the temporary introduced by that invocation resolve to its binder. A local
caller variable, imported name or enclosing macro temporary of the same spelling
must not capture it or be captured by it.

When the user supplies a binder and a body, use that supplied binder in an
actual binding form and place the body in its scope. In schematic notation:

```text
with_value!(item = calculate (), {
    use_item item
})
```

A candidate expansion is `let item = calculate ()` followed by the supplied
body. The caller-supplied `item` in the body should resolve to the supplied
binder; the initializer should retain the preceding scope. This requires the
expander to apply the binding form's scope to the right regions, not simply
preserve all identifiers unchanged. Test nested `with_value` forms and same-name
outer bindings, as well as recursive groups and simultaneous pattern binders.

### Introduce names the caller can use

For a macro that generates declarations, prefer accepting the desired name
explicitly, for example `make_getter!(get_temperature, temperature)`. The
caller-supplied binder can then become the generated declaration name. This
still requires an explicit policy for which declaration contexts permit it,
what surrounding region can refer to it, publication and collision checking.
It does not imply that module-level shadowing is permitted: current Ash rejects
conflicting file-wide imports and declarations.

A transformer that derives `get_temperature` from `temperature` needs a
separate operation to choose a context for the derived identifier. Merely
constructing the desired spelling is insufficient. Alternatives include
requiring the output name as an argument, an explicit caller-context identifier,
or a declaration-generation facility that states its visibility. Compare them
before selecting one, and report a conflict rather than silently replacing an
existing declaration.

### Deliberately use the caller's context

A macro may intentionally refer to or introduce a name in the invocation
context when passing it explicitly is inadequate. For example, a form might
make an implicit `context` binding available inside its caller-supplied body.
A separate, visibly context-selecting operation could create that identifier
using the call-site syntax as its context, analogous to
[Scheme's `datum->syntax`](https://www.scheme.com/tspl4/syntax.html). This is
an intentional deviation from the default treatment of generated names.

The operation must specify which syntax supplies context, which namespace and
scope it affects, and whether it creates a reference or binder. It should have
examples for absent bindings, shadowing, duplicate declarations and nested
expansion. Provenance and diagnostics should identify the explicit context
operation and affected source. It must not itself bypass access, opacity,
resource or continuation checks. Compare this facility with explicitly supplied
binders and ordinary parameters before requiring it.

### Compare identifiers by the intended meaning

A macro may need to check whether two references name the same declaration or
whether two proposed binders would conflict. A spelling comparison is not
sufficient: an imported alias can have a different spelling for the same
identity, and one spelling can denote different bindings. Conversely, literal
punctuation or a contextual keyword may need a spelling comparison.

Scheme distinguishes [free-identifier and bound-identifier comparison](https://www.scheme.com/tspl4/syntax.html)
for these purposes. Ash could expose similar operations, but their behavior for
unresolved names, namespace roles, aliases, expansion phases and ambiguity needs
specification. Do not equate comparison of free references with duplicate
binder checking, or use either to silently select an interface implementation.

### Coverage by category

The tactics should be tested across the following categories, not only ordinary
local variables. The right-hand column identifies questions for the comparison;
it does not add current semantics.

- **Local terms and patterns:** template temporary versus caller term;
  sequential and recursive scopes; same-spelled pattern binders; supplied
  binder and body.
- **Globals and module imports:** same-module helper; targeted import and
  rename; qualified module alias; caller conflict; facade re-export; private
  helper policy.
- **Types and constructors:** type parameters, local nominal shadowing, paired
  `newtype` names, constructor patterns, imported and opaque constructors.
- **Interfaces and methods:** identities, aliases, caller shadowing, separate
  implementation-fact imports and evidence availability.
- **Effects and operations:** effect identity and parameters, qualified
  operation, row-tail variables, handler selection and caller-supplied effects.
- **Resource and region names:** fresh type identity and term handle,
  preceding initializer scope, body scope, escape and completion checks.
- **Macro and syntax names:** imported aliases, nested expansion,
  syntax-keyword conflicts, definition and invocation contexts.
- **Generated declarations:** caller-supplied and derived names, collisions,
  visibility, re-exports and separate compilation.
- **Contextual capabilities:** `resume`, `discard` and `retain` under nested
  handler clauses and their ordinary admission checks.

For each applicable case, compare a handwritten target program with generated
syntax, then vary caller and definition names, aliases, import routes and
nesting. Assert resolved identities and checked behavior, not just printed
expansion. Include expected rejections and causal diagnostics. Evidence
selection and capability admission require their own observations even when
all identifier identities are correct.

## Diagnostics and provenance

The goal is a useful error in the original program even when checking detects
it in an expansion. Consider:

```text
if 42 then 1 else 2
```

A diagnostic should identify `42` as the expression whose type conflicts with
the required Boolean condition and, when useful, identify the expansion and
its syntax definition. Provenance can map the generated check to `42`; it does
not alone establish the phrase “condition of if”. Such wording requires a
retained role, a declared constraint, or a macro-authored diagnostic. A
truthful generic error with correct locations is preferable to an unsupported
explanation.

Branch mismatch and generated operations can have multiple causal inputs.
Origins therefore need to represent more than one span or a single parent
chain where a transformation combines inputs. Record, as applicable:

- the original source of each spliced fragment;
- the template or transformer location that introduced generated structure;
- the invocation and nesting of expansions; and
- input origins used to derive generated syntax.

Retain the relevant causal relationships through parsing, resolution, checking,
elaboration and Core transformations. Preserve the original structured reason,
facts and causal labels in human and machine-readable diagnostics. Choose a
primary location using the actual causes; show additional caller and definition
locations when they explain the error. Do not infer author responsibility from
provenance alone. A procedural transform should preserve origins on splicing
and record them when constructing or deriving syntax. A text conversion that
loses context and origins must make that loss explicit.

A malformed invocation, an invalid transformer output, a generated program's
type error, and a transformer execution failure are different cases. Each
needs a meaningful structured result. Macro authors may need operations for
reporting an error at a particular captured fragment, with related locations;
these operations must not replace ordinary compiler checks or claim unverified
facts.

An expansion viewer and stepper could show each intermediate form, its origins
and binding identities. The [Racket macro debugger](https://download.racket-lang.org/releases/9.3/doc/macro-debugger/index.html)
illustrates this kind of tool. Normal errors should remain useful without
requiring the user to read generated code. A full expansion trace can be
available on demand, with a concise default when it adds causal information.

## Constraints

- Current language rules and accepted decisions remain authoritative until
  changed through the applicable proposal or decision workflow.
- Minimize the semantic Core and the general checking and inference rules
  required by a program, while preserving its complete established obligations.
  A smaller total implementation is an aspiration, not a substitute for that
  criterion.
- Expansions cannot bypass resolution, typing, effects, resource, continuation
  or completion checks. Hygiene is not semantic equivalence or a safety proof.
- Preserve caller and definition binding contexts through nested expansion;
  expose intentional context changes explicitly.
- Preserve causal diagnostic information through later transformations,
  including multiple relevant input locations and expansion nesting.
- Define parsing, scope, import and module behavior without making syntax
  availability depend on undeclared ambient compiler state.
- Keep syntax expansion distinct from typed optimization and whole-program
  transformation; establish preservation evidence where an existing program
  is transformed rather than defined by its expansion.
- Do not assume a macro can implement runtime behavior or checks that its
  target representation cannot express.

## Migration candidates and size

Initial candidates are surface presentations that already converge under
[current elaboration](../../spec/elaboration.md#surface-erasure): equational
clause groups lower to structured matches; operational multi-parameter and
anonymous functions use tuple-domain functions and matches; nontrivial local
binding patterns use an irrefutable one-arm match. A macro implementation must
preserve currying versus tuple domains, recursive scope, pattern coverage,
generalization, effects, evaluation and source diagnostics. Moving the
presentation does not remove the general function, match or checking rules.
Operator notation is conditional on suitable ordinary operations and preserved
semantics; no operator rewrite is established by this note.

Longer-term candidates include effects and handlers, scoped resources and
cleanup, hooks and registration, interface evidence, and nominal identities.
These require typed elaboration or general rules that establish their actual
contracts. The accepted effects package is a concrete direction but is not
implemented; its explicit continuation-use gap remains. Current resource,
cleanup and hook carriers have ownership, authentication and completion
obligations that a surface rewrite alone does not eliminate. The effects and
resource slice must determine which machinery can be replaced, which is
shared and which remains necessary.

On 2026-11-04, the current syntax grammar had 94 named productions across 231
EBNF lines. The lexer, parser and surface representation had 11,214 Rust
lines; all Rust files under `src/` had 319,540 lines. These are raw line
counts including comments and tests, not counts of independent features or
removable compiler logic. Grammar productions may move while their syntax and
supporting rules remain, and macro definitions add their own syntax.

A rough planning scenario for the first facility assumed 4,000–10,000 new
compiler lines, removal or consolidation of 1,000–4,000 compiler lines, and
500–2,000 lines of Ash library code: a net increase of 500–11,000 lines.
These are uncalibrated judgments, not measured outcomes or confidence bounds.
They include neither a WebAssembly backend nor a self-hosted compiler. There
is no supported forecast for the eventual net reduction. More relevant
measures are the Core forms and checking rules a program requires, the
compiler components present and loaded, and the work actually performed.

## Evidence and experiments

Before selecting a design, compare rules-only expansion, shared declarative
and procedural syntax objects, and a token-oriented or hybrid interface.
Compare natural keyword-led syntax with explicitly delimited invocations. Use
the same corpus and distinguish unavailable features from implementation bugs:

1. The `if` example, including nested forms, precedence, a non-Boolean
   condition and incompatible branch types.
2. An effect request wrapper that evaluates an effectful input once and
   preserves handler selection and evaluation order.
3. A handler or resource wrapper with a caller-supplied binder, nested
   shadowing and valid and invalid continuation or resource uses.
4. Repeated declarations or clauses that test whether procedural computation
   provides a material benefit over declarative rules.
5. A bounded fragment of the accepted effects elaboration, recording required
   row, identity, continuation, context and checking information; identify the
   exact point at which surface expansion ceases to suffice.

For each, compare parsing and ambiguity, binding identities, evaluation and
effects, generated structure validation, errors and their causal spans,
separate-module behavior, the required Core and checking rules, and tooling.
Include aliases, definition-site
helpers, nested macro calls, repeated generated names, malformed input and
invalid output. Check both human and structured diagnostics, including
multiple origins and a failure after later elaboration. Compare equivalent
handwritten target programs and rejected cases; do not transfer their results
to untested effect or resource combinations.

For representative programs, distinguish compiler artifact size, loaded or
initialized components and actual compilation work. Include a program with no
explicit effects, one importing an effectful function, and one whose macro
expansion introduces a relevant construct. Account for default allocation and
other shared requirements. Count general Core forms and rules independently
from optional feature-specific paths, and trace retained or replaced checks.
Do not treat a reduced total line count, fewer source keywords or moving code
into Ash as proof that a program requires fewer rules.

A future bounded prototype could test whether the shared syntax-object model
supports this corpus while fitting the parser and resolver boundaries. Its
comparison criteria are the cases and obligations above, implementation
complexity, quality of errors and information needed at each phase. Record
both successful and contrary observations. Retain a prototype only as named,
bounded design evidence if it changes the comparison; otherwise discard it.
Neither outcome establishes product semantics or authorizes production code.
This draft alone does not authorize a prototype or select an implementation.

## Open questions

- Which natural syntax forms and output categories are essential, and which
  should remain delimited or ordinary functions?
- How are syntax names imported, scoped, re-exported, shadowed and kept
  compatible with existing identifier uses? How are conflicting forms resolved?
- Which fragment, literal, repetition and precedence rules give useful syntax
  without requiring arbitrary grammar extensions?
- Which binding model covers Ash's term, type, constructor, effect and hidden
  capability boundaries, including intentionally introduced names?
- Which syntax objects and operations can remain stable as Ash evolves? What
  happens when syntax is converted to tokens, text or plain data?
- How are macro code, dependencies, compile-time effects and declared inputs
  built, cached and isolated? What limits and failure behavior are appropriate?
- Which role or constraint information can improve messages without baking a
  macro's unverified claims into type checking? How are origins and structured
  diagnostics retained across modules and Core boundaries?
- Which effects work is expressible as source expansion, which needs resolved
  or typed transformations, and which requires additional language or runtime
  mechanisms? What preservation and one-shot evidence is needed in each case?
- Which general Core forms and inference, verification and composition rules
  cover each feature? Which current special cases can then be removed without
  losing established facts, independent validation or required diagnostics?
- How are compiler services selected from source, imports, inferred contracts
  and generated code, and what is the minimal shared foundation?
- Which Ash-defined compiler interfaces and builtin operations support both
  the current Rust compiler and a future Ash compiler, including a
  browser-hosted compilation path?
