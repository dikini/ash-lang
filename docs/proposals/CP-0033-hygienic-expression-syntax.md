# CP-0033: Hygienic Expression Syntax

- ID: `CP-0033`
- Status: accepted
- Related: [DN-0062](../design/DN-0062-hygienic-surface-macros.md),
  [first-slice design](../design/macros/first-slice.md),
  [TASK-0067](../tasks/TASK-0067-expression-macros.md),
  [AD-0005](../decisions/AD-0005-parser-architecture.md),
  [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md).

> This proposal records the accepted first expression-macro slice. It is not
> current Ash; no macro implementation or supporting experiment is claimed.
> Amended AD-0005 records the parser decision; TASK-0067 owns delivery.

## Current behavior

The [surface grammar](../../spec/syntax.md#grammar) is fixed. It has no syntax
declarations, syntax imports, template splices, or procedural macro entry.
`if`, `then`, `else`, and `syntax` are currently ordinary identifier spellings;
`$` is not admitted punctuation. The compiler-owned modules do not include a
syntax service. See [lexical structure](../../spec/lexical-structure.md#tokens)
and [builtin names](../../spec/name-resolution.md#compiler-owned-cell-module).

Modules are passive, canonicalized, and acyclic. Imports precede declarations;
only a module's own declared imports create its visible dependencies. Names
resolve to stable identities before typing. Current lexical rules distinguish
simultaneous globals and recursive groups, sequential locals, pattern scopes,
type/constructor scopes, and hidden continuation capabilities. Public/private
and opaque access is checked at module boundaries. See
[name resolution](../../spec/name-resolution.md).

Checked modules complete lowering, selected evidence, and metadata before
publication. Importers use those checked results without repeating dependency
body checking. Linking constructs a new representation that crosses independent
Core validation. Causal origins and structured diagnostic reasons survive these
boundaries. These obligations remain in this proposal.

## Proposed behavior

### Definitions, imports, and parsing

Add public module-level expression syntax, authored as a template or a checked
Ash function:

```text
pub syntax if $condition:expr then $yes:expr else $no:expr => {
    match $condition {
        true => $yes
        false => $no
    }
}

pub syntax guard $condition:expr then $body:expr => using expand_guard
```

Add targeted syntax import items, including renaming:

```text
import control.syntax (syntax if, syntax guard as ensure)
```

A complete module import does not activate syntax. A selector must name the
selected module's own public syntax export. Local/private syntax, own-module
syntax use, syntax re-exports, and syntax output outside expressions are
rejected in this slice. A defining module may use syntax imported from an
acyclic dependency. Header discovery loads and checks dependencies before body
parsing; it never executes a transformer or permits expansion to add an import.

`syntax` is contextual in these declaration/import forms; existing globals
named `syntax` keep their current parse. The lexer recognizes `$` as a token;
the parser admits it only in matchers and template splices. An out-of-place
`$` produces a syntax error rather than today's lexical unknown-character
rejection. The syntax name begins with a lowercase letter and is not a
reserved word. Its local imported spelling is reserved for unqualified
source-authored term binders/references throughout the importing module.
Qualified member spellings are unaffected. Duplicate syntax imports are errors,
including repeated selection of the same identity. Renaming resolves conflicts.

A matcher contains literal tokens and uniquely named `expr` or `ident`
captures on one logical line. It contains at least one capture, ends in an
expression capture, and separates adjacent captures with literals. Groups,
logical newlines, `$`, and `=>` are not matcher literals. It has no repetition,
optional part, alternative, or executable parser callback. Literal matching
uses spelling and kind, not value identity.

A non-final expression capture stops at its next literal at the current
expression level; complete nested forms consume their own separators first.
An identifier capture consumes one identifier and requires its following
literal. The final expression capture extends to the enclosing expression
boundary. Syntax forms have loose prefix precedence, like `match`, and are not
application primaries or infix operators. Parentheses delimit use as an
argument or operand. There is no ordinary-application fallback after a syntax
name is selected. The design companion fixes nesting, stop-token, newline,
precedence, and recovery cases in
[matchers and expression boundaries](../design/macros/first-slice.md#matchers-and-expression-boundaries).

### Syntax values and expansion

Templates and procedures share context-bearing tokens, balanced groups, and
protected unexpanded expression fragments. Splicing an expression retains its
original grouping: a captured `a + b` inserted after `f` is `f (a + b)`.
Fragments are grammatical boundaries, not lexical scopes. No expansion is
obtained by converting syntax to text and reparsing it.

Expansion is outermost first, with completed subtrees visited in source order.
Captures are parsed once; a nested transformer runs only if its invocation
survives in the result. Each retained occurrence of a duplicated capture gets
its own internal binder, nominal/region-owner declaration, and nested expansion
identities. Within that occurrence, references still connect to the correct
binder and free caller references retain their meaning. Runtime execution of
one resulting declaration retains the current stable lexical identity policy.

The expansion walk establishes the actual enclosing scopes before calling a
transformer, preserves those scopes in captures, and applies the scope of each
generated binding form to its correct regions. Introduced identifiers carry a
fresh introduction scope and definition context. Caller syntax keeps its own
context. The [scope-set algorithm](../design/macros/first-slice.md#expansion-and-lexical-binding)
selects the unique most-specific binding in the relevant namespace; unresolved,
ambiguous, and duplicate contextual names are rejected. Source-written names
retain their existing scope behavior.

An introduced temporary cannot capture caller syntax. A caller-supplied
identifier used as a generated binder can bind its caller-supplied body, while
a nonrecursive initializer remains in preceding scope. The explicit
`caller_identifier` operation intentionally chooses the invocation context;
ordinary definition-site references and supplied binders need no escape.
The operation grants no extra access, implementation evidence, or hidden
continuation capability.

Syntax lookup has its own retained context. A spliced invocation keeps the
caller's syntax imports; a template invocation keeps the definition's imports.
A caller's same-spelled syntax name cannot redirect a generated ordinary
identifier or definition-site invocation. Fresh private identifiers have no
syntax binding. The caller context of a constructed invocation is defined by
its leading identifier, not inferred from an arbitrary argument.

### Definition-site authority

Templates are checked for syntactic validity at definition time using
category-correct capture placeholders; this does not resolve their free names.
When a template is expanded, its literal free references resolve in the
defining module's checked lexical environment after generated binding structure
is known. An unresolved or inaccessible name then fails ordinary resolution;
an unused template does not fail for that name. A caller's locals, imports, or
aliases cannot redirect these references. Captured identifiers and expressions
retain their contexts, and introduced local binders retain ordinary hygiene.
Qualified references resolve the alias in its retained context, then its actual
exported member. Procedurally constructed definition-context names use the same
expansion-time lookup.

Publishing syntax permits references to resolve with the defining module's
lexical access. Compiler-issued identifier contexts select that checked
environment; spelling and diagnostic origins cannot select it. Ordinary
resolution checks the declaration and applicable access and import rules, then
records its stable identity. The checked declaration facts and executable
dependency closure needed by ordinary checking and linking survive. This does
not add an ordinary import to the caller or require a separate per-reference
authorization object.

A macro owner can publish syntax using its private helper, private nominal, or
own opaque constructor, as it can publish a helper function doing the same.
Neither that owner nor its macro gains access to a dependency's unexported
member or withheld constructor. Caller source cannot directly name the private
declaration, and spliced/caller-context identifiers cannot acquire its access.

A definition-site method name retains its `MethodId` but does not capture the
definition's implementation imports. Its generated use satisfies ordinary
caller/lexical evidence obligations. A checked definition helper can retain a
chosen implementation. Hidden `resume`/`discard`/`retain` capability admission
follows the actual expanded handler/function structure and current checking.

### Checked Ash transformer host

Add the canonical `@builtin.compiler.syntax` module and the
[Ash-defined syntax interface](../design/macros/first-slice.md#ash-syntax-interface).
That section specifies the ordinary nominal data, opaque handles, total
operation results, parse failure preservation, origins, and callable signatures
included in this proposal. It is the accepted interface contract, independent
of Rust layouts or compiler-internal AST types.

The syntax interface's `TokenKind` depends on a shared public lexical and
metaprogramming vocabulary. The current lexical specification defines token
classes and spellings, but not public constructor names. Defining those names
and their mapping is a general language-definition concern; this proposal
identifies the dependency and the cases its interface needs. The implemented
interface must document the shared mapping and spelling validation and provide
conformance evidence that implementations of the same interface version agree.
Choosing the names is not a separate macro-design acceptance condition.

A procedural transformer is an ordinary unconstrained, monomorphic global in
the defining module. Its usual signature is `Input -> MacroResult ! {Ops}`,
including current implicit default allocation. Admission inspects its actual
function type: domain `Input`, result `MacroResult`, and a closed latent row
containing only default allocation and optionally canonical `Ops`. Other
outward effects and open rows are rejected. No function-value effect subtyping
is introduced. `Ops` denotes the syntax module's canonical service effect,
not an arbitrary same-spelled effect.

The compiler links already checked transformer/helper fragments into a
compile-time entry, independently validates that new Core program, and invokes
the actual Ash body with an authenticated `Input`. No source `main` is required
in the macro module. Reusing the same validated compile-time program does not
repeat dependency body checking or Core validation. A changed linked program
returns to validation; each input/output crosses its own checked host boundary.

The host supplies default allocation and syntax services, with no native,
network, filesystem, clock, target query, or ambient compiler mutation service.
Opaque handles cannot be forged from numbers, spellings, pointers, or origins.
Output decoding authenticates nominal shape, handles, and origins.
The host transfers the complete result to compiler storage before releasing
its evaluation root. Failure closes the invocation and publishes no partial
expansion, preserving primary and teardown failures.

Transformer steps, service work, output size, and recursive expansion are
bounded by compiler work/storage/depth policy. Exhaustion is a structured
expansion failure; numeric budgets are implementation policy. Equal semantic
inputs produce equal results modulo fresh identity renaming and possible
resource exhaustion. Exposed operations do not reveal raw identity numbers or
allocation order. The source, contexts, checked dependency closure, interface
version, and relevant semantic options determine any retained result's validity;
no persistent cache is required by this slice.

### Admission and diagnostics

Each output must parse as exactly one expression with no trailing, missing,
invalid, or recovery-bearing structure. Nested invocations expand through the
same boundary. The result then crosses ordinary resolution, checking,
elaboration, linking, and independent Core validation. Generated syntax cannot
supply a type, builtin authority, selected evidence, or validated Core fact
without those checks.

Retain source origins, construction origins, ordered invocation/definition
frames, and every causal input to a multi-fragment failure. Preserve ordinary
structured reasons and facts in human and JSON output. Malformed definitions,
imports, invocations, authored rejection, evaluator/service/resource/output
failure, and ordinary generated-program rejection remain distinct causes.
Macro-authored text does not replace compiler-owned diagnostic localization.
The compiler need not infer a DSL-specific role description from a source span.

## Semantic delta

- Add public expression syntax declarations, targeted syntax imports/renames,
  contextual `syntax`, and `$` tokens usable as declaration-local splices.
  Misplaced `$` changes from a lexical to a syntactic rejection.
- Add imported loose-prefix matchers, protected expression fragments, and a
  deterministic ordered expansion phase integrated with lexical scoping.
- Add hygienic lexical and syntax contexts, distinct generated declaration
  occurrences, explicit caller-context construction, and context-aware
  duplicate/ambiguity checking across existing namespaces.
- Resolve definition-context references using the checked defining environment,
  including its private and opaque declarations, without exposing their names
  or capturing interface implementation availability in caller scope.
- Add an Ash-defined canonical syntax service, compile-time entry and checked
  bridge, bounded execution, output admission, and expansion provenance.
- Preserve the semantics and parse of existing valid modules without syntax
  imports or the new declarations. Previously invalid `pub syntax` declarations
  become available without requiring syntax imports. Existing invalid inputs
  involving the new token/forms can receive new diagnostics. Preserve current
  Core/checking/runtime obligations on every expanded program.

## Affected specification areas

- [Lexical tokens](../../spec/lexical-structure.md#tokens): contextual `syntax`,
  declaration-local `$`, and module-local syntax-name reservation.
- [Surface grammar](../../spec/syntax.md#grammar) and
  [precedence](../../spec/syntax.md#precedence-and-associativity): definitions,
  import selectors, matcher restrictions, fragments, and prefix boundaries.
- [Module identity](../../spec/name-resolution.md#module-paths-and-identity),
  [imports](../../spec/name-resolution.md#imports-and-namespaces),
  [type/constructor scope](../../spec/name-resolution.md#type-and-constructor-scope),
  [visibility/opacity](../../spec/name-resolution.md#public-private-and-opaque-declarations),
  and [local scope](../../spec/name-resolution.md#local-scope): syntax contexts,
  import staging, definition-context resolution, generated declaration
  occurrences, and retained current scope/capability policies.
- [Static semantics](../../spec/static-semantics.md#globals-and-modules):
  syntax publication, transformer admission and canonical syntax-service types;
  existing typing and evidence rules check expansions.
- [Elaboration](../../spec/elaboration.md#surface-erasure),
  [linking](../../spec/elaboration.md#module-linking-and-entry-generation), and
  [validation](../../spec/elaboration.md#validation-boundary): syntax erasure,
  authorized reference closure, compile-time entry and validated boundaries.
- [Initial execution](../../spec/dynamic-semantics.md#initial-configuration):
  the compile-time service host, result transfer, failure, and bounded work.
- The [overview](../../spec/README.md), a new syntax-expansion specification
  chapter if needed for organization, and current compiler/tool documentation.
  A new chapter would organize these rules rather than add an authority level.

The accepted amendment to AD-0005 extends its closed built-in assembly with one
expression-prefix mechanism parameterized by a data-defined imported matcher
environment. Its lexer/precedence/recovery/projection boundaries remain. The
amendment is architectural authority separate from this proposal and remains
unimplemented under TASK-0067.

## Resulting specification truth

After the complete product transition is integrated into `main`, the
specification defines expression syntax and the Ash compiler-service interface
above as supported language/compiler behavior. It states that expansion
preserves lexical and syntax context, records checked declaration identities
and causal origins, and leaves generated programs subject to normal checking.
It describes only the implemented first-slice categories and imports; the broader DN-0062
alternatives remain informative. No existing convenience is claimed to have
moved into a library or ceased to require its current checks.

## Interactions

Current effect, resource, region, continuation, interface-evidence, allocation,
and completion rules independently constrain expanded programs. For example,
legacy `resource cell` still requires the caller's specified direct builtin
import; expression expansion cannot add it. A wrapper's evaluation order/count
is that of its output, not a property guaranteed by hygiene.

The compile-time entry and final runtime program are distinct checked host
boundaries. Syntax services do not become runtime interpretations or program
image constants. Generated output must remain consumable by the existing
interpreter and supported build/image path after expansion. Importers reuse
completed dependencies, while each newly linked Core program receives its
independent validation. New references must retain original import provenance
and private declaration closure through those consumers.

This proposal does not reconcile with or depend on the effects redesign.
Effects work may take this contract into account; the expression-only slice
does not determine its elaboration strategy.
[DN-0030](../design/DN-0030-typed-compiler-macros-and-hooks.md)'s typed hooks,
registration, and optimization questions remain separate.

## Non-goals

- Declaration/type/pattern output, pattern captures, local/private syntax,
  own-module syntax use, syntax re-exports, matcher repetition or arbitrary
  grammar replacement.
- Typed compiler transformations, inferred-type queries, ambient plugin
  registration, or bypasses of ordinary type/effect/evidence/resource checks.
- Retiring existing source/Core forms or claiming a net reduction in compiler
  size from introducing the facility.
- Persistent macro caches, a CLI expansion debugger, self-hosting, a Wasm
  backend, browser-hosted compilation, or runtime access to the syntax service.
- Effects redesign, new resource semantics, external communications, or an
  active implementation task created by acceptance alone.

## Required evidence

Retain all [M01–M14 cases](../tasks/TASK-0067-expression-macros.md#acceptance-evidence)
through implementation and one product checkpoint. They cover positive and
negative parsing/grouping, real checked-Ash execution, term and non-term
hygiene, copied declaration occurrences, deliberate capture, private authority,
imports/DSL composition, current effect/resource/evidence checks, bridge
round-trips, provenance, teardown, bounded failure, reproducibility, module/Core
boundary mutations, and existing compiler consumers.

Use one real file-graph acceptance path through the public compiler driver,
not independently passing component helpers. A syntax module with a computed
transformer and template, a private helper and imported dependency, another DSL,
and a renamed syntax importer must compile, link, and execute with correct
bindings and diagnostic variants. Compile supported generated output through
the build/image consumer as well as the interpreter. Observe that returned
output survives host-root teardown and that failed expansion publishes nothing.

The [task-owned execution plan](../plans/2026-11-05-expression-macros.md)
records producer/consumer agreements, D0–D4 dependencies, integration ownership,
focused verification, full-gate checkpoints, and the whole-chain estimate.
[TASK-0067](../tasks/TASK-0067-expression-macros.md) retains that plan and
evidence matrix; component work does not close production acceptance. An
independent reviewer
must challenge the boundary map and review the retained end-to-end result.

Update implementation, positive/negative tests, specification, tool docs,
compiler-owned diagnostic declarations/catalogues, and the parser decision in
the product transition. Verify Markdown, relative links/anchors, artifact
status, and authority boundaries. Run the focused affected tests and a fresh
`cargo xtask verify` on the pinned integration candidate. If implementation
reveals missing semantics, return to this proposal before choosing them.
