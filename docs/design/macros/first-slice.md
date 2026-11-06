# Hygienic surface macros: first-slice design

This companion to [DN-0062](../DN-0062-hygienic-surface-macros.md) records the
design behind [CP-0033](../../proposals/CP-0033-hygienic-expression-syntax.md).
CP-0033 accepts this first slice, which is not implemented or current Ash.
The parser amendment is recorded in
[AD-0005](../../decisions/AD-0005-parser-architecture.md);
[TASK-0067](../../tasks/TASK-0067-expression-macros.md) owns implementation and
its execution plan. This companion remains design rationale. Examples use
accepted future syntax.

## Scope and choice

The slice adds explicitly imported, keyword-led expression syntax. A module
publishes a matcher and either a template or an ordinary checked Ash
transformer. Callers write natural forms such as `if ready then start () else
wait ()`. Both authoring forms use one syntax representation, one expansion
order, and one account of binding and provenance.

The slice includes nested expansion, caller-supplied identifier binders,
definition-site references across module boundaries, private helpers, and an
explicit caller-context operation. Transformers consume and produce syntax;
they do not receive inferred types, select implementations, or return Core.
Ordinary resolution, checking, elaboration, and independent Core validation
remain responsible for the resulting program.

The selected alternatives are:

| Choice | Reason and cost |
| --- | --- |
| Keyword-led syntax with explicit imports | Provides unmarked DSL notation. A reserved leading spelling and restricted matchers bound ambiguity; some ordinary names need import renaming. |
| Context-bearing tokens, groups, and protected expression fragments | Preserves binding, origins, and grouping without publishing the compiler AST. Requires an Ash-defined interchange and host adapter. |
| Templates and Ash procedures together | Supports substitutions and computed transformations under one contract. Requires a checked-Ash execution bridge in the first slice. |
| Scope sets with checked definition-context lookup | Handles caller binders and definition-site helpers across namespaces. Requires expansion-aware lexical resolution. |

A mandatory punctuation-marked invocation would simplify parsing but would not
meet the natural-syntax goal. Arbitrary grammar callbacks would admit more DSLs
but would expand ambiguity, recovery, and execution obligations. Rules alone
would avoid the host bridge initially but leave computed Ash transformations
unproved. A compiler-AST interface would save some conversion but bind library
authors to compiler representation changes. These are design tradeoffs, not
measured performance claims.

The slice excludes declaration, type, and pattern output; pattern captures;
matcher repetition, alternatives, and optional parts; local or private syntax;
syntax re-exports; and arbitrary parser callbacks. A module may define several
syntax forms but may use only forms imported from dependencies, not its own
forms. This keeps module and compile-time construction acyclic.

An expression may contain ordinary bindings, annotations, `newtype`, handlers,
or resources. Hygiene therefore covers their term, type, constructor, alias,
interface, and effect names even though output is one expression. Hidden
continuation capabilities follow their existing structural scope rules,
separately from identifiers.

The slice adds a facility; it does not yet remove an existing surface form,
Core form, or checking rule. Declaration migrations need a later output
category. Every later migration must identify the machinery removed and
preserve its obligations or propose a semantic change. This design neither
reconciles with nor depends on an effects redesign. Current specified effects
and resources supply independent regression cases. Future elaborators can
consume this boundary or propose a later extension.

## Source forms and visibility

The two definition forms differ only in their implementation:

```text
pub syntax unless $condition:expr then $body:expr => {
    match $condition {
        true => ()
        false => $body
    }
}

pub syntax guard $condition:expr then $body:expr => using expand_guard
```

The braced template is the resulting block expression; its braces are not
quotation delimiters to discard. `$condition` and `$body` splice syntax, not
values. The procedural name must denote an ordinary global in the defining
module with the transformer type below. It may be private. Every syntax
declaration in this slice is public.

The proposed grammar adds the following forms. `matcher_item` and its validity
conditions are described in the next section. `template_block` uses the current
block grammar with named expression and identifier placeholders admitted in
their corresponding positions; it is not an ordinary source block before
substitution. Existing identifier and ordinary import productions remain.

```ebnf
syntax_declaration ::=
  "pub" "syntax" identifier matcher_item { matcher_item }
  "=>" ( template_block | "using" identifier ) ;
syntax_import_item ::= "syntax" identifier [ "as" identifier ] ;
matcher_item ::= literal_token | "$" identifier ":" ( "expr" | "ident" ) ;
```

`syntax` is contextual at a syntax declaration or targeted import item.
Existing declarations such as `pub syntax : Unit -> Int` still parse as
ordinary globals. The lexer recognizes `$` as a token; the parser admits it
only in matchers and template splices and reports a syntax error elsewhere.
Outside those forms, this intentionally replaces the current lexical
unknown-character rejection. `expr` and `ident` are category labels there,
not new global keywords.
The leading syntax name uses a lowercase initial letter, is not an existing
reserved word, and is part of each invocation.

An explicit targeted import activates the syntax name:

```text
import control.syntax (syntax unless, syntax guard as ensure)
```

The importer can use `unless test then action` and `ensure test then action`.
Renaming changes only the leading keyword. It does not rename the template's
references or separators. An ordinary complete import does not activate
syntax. A syntax selector must select a public syntax export of that module;
it does not search transitive dependencies. `pub import` of a syntax item is
rejected in this slice. Ordinary import items keep their current meaning.

Two local syntax declarations cannot export the same name. Two syntax imports
with the same local name are an error, including repeated imports of the same
identity. In a module importing a syntax name, its spelling
is reserved for unqualified source-authored term binders and references
throughout that module. A conflict identifies the source occurrence and syntax
import; renaming the syntax import resolves it. Members after a qualified dot
and literal separator words are unaffected. This prevents an ordinary
application from silently changing meaning. Generated names use their retained
contexts, not a reservation from an unrelated importing module.

The loader first reads each source's fixed import header, canonicalizes its
declared graph, and rejects cycles under the current module rules. Dependencies
are checked before their importers. A module's syntax imports are loaded before
its declaration bodies are parsed. Header discovery does not run transformers,
and expansion cannot add an import or module edge. Existing valid module bodies
without syntax imports or the new declarations keep their current parse and
resolution behavior. Previously invalid `pub syntax` declarations become
available even without syntax imports; that is an intentional addition.

## Matchers and expression boundaries

A matcher is one logical line of literal tokens and uniquely named captures.
At least one capture is required, the final item is an `expr` capture, and
consecutive captures require a literal separator. Captures are `expr` or `ident`; an
identifier capture accepts one ordinary lowercase or uppercase identifier.
Balanced group delimiters, logical newlines, `$`, and the declaration delimiter
`=>` cannot be matcher literals in this slice. Other admitted lexical tokens
can be literals. Literals match token kind and spelling, not a value binding.
Each imported leading name selects exactly one matcher: there is no overload
search or fallback to function application.

For a non-final expression capture, its next literal is the stop token at the
current expression level. The parser completely parses a nested group, block,
match, function, or syntax invocation before considering that surrounding stop
token. A terminator intended as an ordinary unqualified identifier at that
level needs parentheses. An identifier capture consumes exactly one token and
then requires its next literal. The final capture consumes an expression to
the enclosing boundary: a logical line end, enclosing delimiter, or enclosing
syntax capture's stop token.

Syntax invocations occur in expression-prefix positions with the same loose
outer boundary as `match`; they are not juxtaposition primaries or infix
operators. Passing one as a function argument or using it as an infix operand
requires parentheses. The final capture otherwise includes its ordinary
applications and operators. These examples fix grouping for an imported `if`:

| Source | Grouping or outcome |
| --- | --- |
| `if a then b else if c then d else e` | The second `if` is the outer form's final expression. |
| `if a then if b then c else d else e` | The inner invocation consumes its own `else`; the remaining `else` terminates the outer second capture. |
| `if a then b else c + d` | The final capture is `c + d`. |
| `(if a then b else c) + d` | Addition is outside the invocation. |
| `f (if a then b else c)` | One parenthesized invocation is the argument. |
| `f if a then b else c` | Rejected: the syntax name is not an application primary. |
| `if a then b` | Missing `else`, reported as an invocation error. |

At a syntax prefix, the parser commits to its context's selected syntax
identity. Caller syntax retains the caller's imports. Literal invocations in a
template retain the defining module's imports; the eventual caller need not
import those forms. A generated identifier cannot acquire a syntax binding
from an unrelated caller merely because it has the same spelling. Syntax
aliases retain declaration identity and route, independently of term lookup.

Every `expr` capture is a protected, unexpanded expression fragment. When
spliced into output it acts as one expression atom for grouping: `f $x` with
`$x` captured from `a + b` becomes `f (a + b)`. The fragment is not flattened
into `f a + b`. Protection is a grammatical boundary, not a lexical scope;
surrounding generated binders can still scope over its contents. A display may
insert parentheses, but the compiler never obtains expansions by printing and
reparsing text.

The token-complete source invocation, capture ranges, and recovery information
remain available. Missing tokens and recovery nodes cannot become transformer
input, a fragment, or resolver input. A malformed invocation fails even if an
outer transformer would have discarded that capture. Nested invocations are
parsed here but expanded only if retained in the output.

## Ash syntax interface

The new canonical `@builtin.compiler.syntax` module defines the public contract
in Ash terms. Ordinary nominal data describes syntax structure and operation
results; opaque compiler-issued handles retain lexical and provenance facts.
The compiler authenticates these declarations by canonical origin. Copying
their source or matching their spelling supplies no compiler authority.

These proposed data declarations show the structural boundary. `Token`,
`Identifier`, `ExpressionFragment`, `Input`, `Origin`, and `ParseFailure` are
opaque; their constructors are not exported.

```text
pub type Syntax = Syntax(Nodes)
pub type Nodes = NoNodes | MoreNodes(Node, Nodes)
pub type Node = TokenNode(Token, Origin)
    | IdentifierNode(Identifier, Origin)
    | GroupNode(Delimiter, Syntax, Origin)
    | ExpressionNode(ExpressionFragment, Origin)
pub type Delimiter = Parentheses | Braces
pub type Origins = NoOrigins | MoreOrigins(Origin, Origins)
pub type Capture = ExpressionCapture(ExpressionFragment)
    | IdentifierCapture(Identifier, Origin)
pub type CaptureResult = Captured(Capture) | MissingCapture
pub type OriginsResult = Combined(Origin) | MissingOrigins
pub type IdentifierResult = MadeIdentifier(Identifier) | InvalidIdentifier
pub type TokenResult = MadeToken(Token) | InvalidToken
pub type ParseResult = Parsed(ExpressionFragment) | ParseRejected(ParseFailure)
pub type MacroDiagnostic = MacroDiagnostic(String, Origin, Origins)
    | SyntaxDiagnostic(ParseFailure)
pub type MacroResult = Expanded(Syntax) | Rejected(MacroDiagnostic)
```

`TokenKind` is an ordinary closed nominal family covering non-identifier lexical
kinds admitted in expression output, including logical newlines and reserved
words. Parentheses and braces are represented by groups, not standalone
delimiter tokens. A token's kind and original spelling are inspectable.

The public constructor names and their mapping to source spellings belong to
Ash's general lexical and metaprogramming vocabulary. The current
[lexical specification](../../../spec/lexical-structure.md#tokens) defines
token classes and spellings but does not define that public constructor family.
This macro interface depends on the shared vocabulary; it does not define a
separate list or expose Rust lexer discriminants. Its implemented interface must
document the applicable cases and spelling validation, and implementations of
the same interface version must agree on them. The shared vocabulary and its
conformance evidence can be defined alongside the language and tool interface;
selecting its names is not a decision this macro design must settle.

`expression_syntax` returns the fragment's contents as an ordered
syntax sequence and leaves the original fragment intact. Reusing that sequence
instead of `ExpressionNode` explicitly removes its outer grammatical boundary;
nested fragments, contexts, and origins remain. No splice implicitly performs
that conversion.

The module exposes these operations. Types use unqualified names as seen
inside that module. A tuple is one ordinary Ash argument. `Ops` is a canonical
compiler-service effect; each signature has the latent row `{Ops}` plus the
current implicit default-allocation requirement. These are proposed signatures,
not declarations already supplied by Ash.

```text
capture : (Input, Int) -> CaptureResult ! {Ops}
invocation_origin : Input -> Origin ! {Ops}
definition_origin : Input -> Origin ! {Ops}
token_kind : Token -> TokenKind ! {Ops}
token_spelling : Token -> String ! {Ops}
identifier_spelling : Identifier -> String ! {Ops}
expression_syntax : ExpressionFragment -> Syntax ! {Ops}
make_token : (TokenKind, String) -> TokenResult ! {Ops}
parse_expression : (Input, Syntax) -> ParseResult ! {Ops}
fresh_identifier : (Input, String, Origin) -> IdentifierResult ! {Ops}
definition_identifier : (Input, String, Origin) -> IdentifierResult ! {Ops}
caller_identifier : (Input, String, Origin) -> IdentifierResult ! {Ops}
combine_origins : (Input, Origins) -> OriginsResult ! {Ops}
```

`Ops` declares one operation per function above, with the same name, domain,
and result and the current required pure outer operation arrow. The functions
are ordinary request wrappers with the shown latent row. The compile-time host
interprets those requests; it does not expose host-language objects.

Sequences, groups, and result variants use ordinary data constructors.
`make_token` rejects a spelling inconsistent with its kind and cannot construct
identifiers or unbalanced groups. `parse_expression` parses exactly one
expression with retained contexts and protected fragments. It does not resolve
names, expand nested invocations, or run another transformer. A `ParseFailure`
retains structured parser causes and origins; returning `SyntaxDiagnostic`
preserves them in the final diagnostic. `capture` uses matcher capture order
and is total, including negative and out-of-range integer indices. It returns
only this invocation's captures.

`fresh_identifier` creates a distinct private introduction context each time;
reuse the returned identifier for its binder and references. It has no syntax
binding, even if its spelling names imported syntax. `definition_identifier`
uses the syntax declaration's checked definition context and this expansion's
introduction scope. `caller_identifier` uses the invocation's lexical and
syntax contexts without the introduction scope. Both resolve according to the
generated occurrence's namespace and position. Only the last operation is the
explicit hygiene escape. Spelling is checked against current identifier rules;
string conversion for display never restores context.

The compiler issues `Input` for one invocation. The transformer cannot choose
another defining module, supply a raw context, or construct an `Input` from
ordinary data. Origins supplied to identifier construction are diagnostic
locations, not authority. Introduced tokens and identifiers also retain their
construction operation's origin. `combine_origins` creates a causal origin
from a nonempty ordered origin list and retains the current expansion frame.
Every output node receives that frame even when it preserves an input's
primary source origin.

Handles are valid within their issuing invocation and compilation. Raw numbers,
pointers, serializations, and source spans cannot recreate them. Output
admission rejects stale or foreign-compilation handles. The first slice exposes no raw scope IDs,
identity ordering, or binding-equivalence query. These omissions keep
procedures independent of allocation order and avoid pretending an unresolved
fragment already has final binder identity.

The usual transformer signature is `Input -> MacroResult ! {Ops}`, including
implicit default allocation. Admission requires an unconstrained, monomorphic
`Input -> MacroResult` function whose actual latent row is closed and contains
only default allocation and optionally the canonical `Ops` instance. This
inspects its exact function type; it does not coerce an arrow through effect
subtyping. Ordinary helper calls and source handlers still obey current Ash;
the execution host supplies no native
callbacks, network endpoints, filesystem, clock, target query, or ambient
compiler state. The new effect is admitted only by the compile-time entry.
Runtime entry admission does not gain an interpretation for it.

These Ash contracts, opaque-handle behavior, and operation failures are the
compatibility boundary. Rust and future Ash compilers can use different
internal trees, arenas, handles, and caches. Neither compiler language nor a
native host API appears in the public types. A browser-hosted compiler would
need to implement the same contract and execution host; this slice supplies
neither a Wasm backend nor browser execution evidence.

## Expansion and lexical binding

The selected algorithm interleaves lexical scope establishment with expansion,
then performs final name resolution before typing. It does not resolve a
captured expression before a generated binder can bind it.

Each identifier has spelling, lexical context, syntax context, and origin.
A lexical context is a set of compiler-issued scopes. A binding has its
spelling, namespace, scope set, and stable identity. A reference selects the
binding whose scope set is the unique most-specific subset of its own context
in the required namespace. No candidate means an unresolved-name error;
incomparable maximal candidates are ambiguous and rejected. Equal contextual
binders in the same
binding group are duplicates. For handwritten source this reproduces the
current scope and duplicate rules; different macro contexts can distinguish
same-spelled introduced names.

The expansion walk follows this order:

1. Establish simultaneous module declaration and import scopes. Visit each
   ordinary binding form according to its current lexical policy. Add a fresh
   lexical scope to its binder and exactly the regions it binds before
   expanding invocations in those regions. For sequential `let`, visit the
   initializer first; the new scope covers only the following remainder.
2. At an invocation, retain the already established enclosing contexts of its
   captures and caller. Allocate one fresh introduction scope. Instantiate
   literal template identifiers in the definition context plus that scope, or
   run the procedural transformer with the corresponding `Input`. Splices
   preserve their contexts; they do not receive a generic replacement tag.
3. Parse output as one expression. Walk its new binding forms and nested
   invocations. Do not reapply already established enclosing scopes to newly
   introduced definition-site identifiers. For each retained fragment occurrence,
   establish its internal lexical scopes when visiting that occurrence.
4. Complete each subtree before the next sibling in source order. After all
   expansion, resolve every occurrence to its stable identity and apply normal
   namespace, authorization, and contextual-capability checks. Then typecheck
   and elaborate the resolved result.

This is outermost-first expansion, not early expansion of captured arguments.
A capture is parsed once as an unexpanded structure. Its enclosing scopes are
available to the transformer, but its internal binders have not been resolved.
A retained nested invocation expands at each occurrence in output; a discarded
one does not execute its transformer. Repeated splices share input structure
only immutably. Each output occurrence receives its own internal lexical scopes,
local binder and nominal/region-owner declaration identities, and nested
expansion identities. Visiting one copy cannot change another or retarget a
free caller reference.

In particular, duplicating a captured block containing a `let`, local
`newtype`, region declaration, and nested syntax creates distinct declarations
in the two output occurrences even though their source origins are shared.
Within each copy the uses still connect to that copy's declarations. Repeated
runtime execution of one resulting declaration retains the current stable
lexical identity policy; it does not create a new nominal identity per call.
Parse-once capture is therefore distinct from per-occurrence expansion and
resolution, and from reusing a completed imported module.

A template-introduced `temp` binder and its references have the definition
context and introduction scope. A spliced caller `temp` lacks that scope and
cannot be captured. If the template uses a captured `$name:ident` as a `let`
binder, its fresh lexical scope is added to the captured body but not the
initializer. Same-context caller occurrences in the body bind to it. A
caller-selected binder needs no hygiene escape.

Recursive groups add their simultaneous scope to every initializer and the
following remainder. Function and match-pattern scopes cover only their
bodies. Local `newtype`, its constructor, parameters, representation, and
following remainder use their current distinct regions. Resource and region
type and value binders retain their different initializer/body policies.
Implementation must cover these policies through the resolver's scope
operations rather than apply one scope to an entire generated block.

Syntax lookup is separate. Parsed invocations retain the selected syntax
identity. For newly constructed tokens, the identifier's syntax context
selects only an export available in that context. Normal term lookup cannot
activate syntax; a failed syntax lookup does not consult caller imports.
Templates can use a dependency's syntax without exposing it to callers.
Evaluation order and duplication follow the checked expansion; hygiene alone
promises neither single evaluation nor effect preservation.

The invocation's caller context is the context of its leading keyword
identifier, including the lexical scopes established at that position. A
constructed nested invocation may therefore have a definition-derived caller
context while its arguments retain different source contexts. The API does
not choose an arbitrary capture's context or replace mixed contexts with one.

## Definition references, authority, and linking

Templates are parsed for syntactic validity at definition time using
category-correct placeholders, without resolving free names. When expanded,
literal free references resolve in the defining module's checked environment
after generated binding structure is known; a missing or inaccessible name
then fails ordinary resolution even if a caller has a matching name. Unused
templates do not fail for unresolved names. Captured identifiers and
expressions retain their contexts, and introduced local binders retain ordinary
hygiene. Procedurally constructed definition-context names use the same
expansion-time lookup; diagnostics retain invocation and construction causes.

Publishing `pub syntax` permits its definition-context references to use the
defining module's lexical access. Compiler-issued contexts select that checked
environment; ordinary resolution checks each actual declaration, namespace,
access, and import route, then records its identity. Spelling and origin handles
cannot create definition context. Nested syntax preserves each identifier's
context. The defining environment does not become an ordinary caller import.

The owner may deliberately publish syntax using a same-module private helper,
private type, or its own opaque constructor, just as it may publish a helper
function using those declarations. A dependency's unexported members and
withheld opaque constructors remain inaccessible to that owner and its macros.
Ordinary caller source still cannot name the macro module's private helper or
constructor. A captured caller identifier cannot gain definition authority by
being spliced into output. A caller-context identifier keeps caller access.

Qualified references first resolve the alias in its retained context, then
select a member through that module's actual exports. The member is not an
independent unqualified lookup. Targeted renames, complete aliases, and facade
routes preserve original identity and causal import provenance. A caller's
same-spelled alias cannot redirect a definition-site reference.

Syntax exports retain the checked declaration closure needed to typecheck
authorized references and the completed executable fragments and dependencies
needed when those references survive into runtime code. Linking follows the
checked dependencies and fragments without placing private names in caller scope.
It does not recheck dependency bodies, rebuild their evidence, or treat a checked module as
independently validated Core. The new linked representation still receives
independent validation under
[AD-0007](../../decisions/AD-0007-typed-core-dialects.md).

Name authority does not capture interface implementation availability. A
generated method occurrence has its original `MethodId`; ordinary caller and
lexical evidence rules satisfy its obligations. If a macro needs a definition's
chosen evidence, use a checked helper there. Nor does identity install a
handler or grant a continuation capability. `resume`, `discard`, and `retain`
resolve against the actual expanded handler structure, including the existing
prohibition on capturing a clause capability in a nested function. Spelling
or provenance cannot supply a hidden `ResumeId`.

Other current admission rules still apply to the caller's resulting module.
For example, emitting legacy `resource cell` does not create its required
direct builtin import. A macro cannot emit that import in this expression-only
slice. This differs from retaining an authorized imported name such as a named
generic-cell API reference.

## Compiler-to-Ash execution and staging

A syntax-defining module completes ordinary parsing, expansion of its imported
forms, resolution, typechecking, lowering, selected evidence, and metadata
before publication. The compiler then publishes its syntax matcher, template
or transformer identity, definition environment, source origins, and
declared dependency closure. An imported module is checked once at that
boundary, as required by
[AD-0006](../../decisions/AD-0006-front-end-semantic-boundaries.md).

For a procedural invocation, a compiler-created compile-time entry selects the
checked transformer and closes its declared helper dependencies. It links
retained fragments into a new compile-time Core program, supplies default
allocation and the syntax service interpretation, and independently validates
that program before execution. The macro module needs no source `main`.
Reusing an unchanged validated compile-time program does not revalidate it at
each invocation; each fresh `Input` is checked at the host-call boundary. A
changed linked program returns to independent validation.

The host converts captures into ordinary Ash interchange data containing
opaque handles, calls the checked Ash function, and receives `MacroResult`.
It does not substitute a Rust implementation for the transformer body. Syntax
operations interpret only the invocation's authenticated input and definition
environment. Output decoding checks nominal constructor identities, complete
data shape, token validity, handle provenance, and allowed expression category.
Ordinary resolution and checking then check the generated program in its caller.

The host owns one fresh evaluation allocation root and service state. After
success it transfers the complete output and handle/origin closure to
compiler-owned storage before closing that root. It retains no Ash value or
backing allocation after its owner closes. A rejected result, evaluator
failure, invalid output, or transfer failure closes the activation and
publishes no partial expansion. Cleanup preserves the primary failure and any
teardown failure under the existing runtime guarantees.
Rejected diagnostics and available failure data also transfer to compiler
storage before root teardown; a failed transfer uses the bounded host failure
report rather than retaining an allocation from the closed root.

The host provides no ambient compiler mutation. Expansion cannot publish a
module, read a file, inspect a clock or target, invoke native callbacks, or
change another module's syntax environment. It charges transformer steps,
syntax service work, output size, and recursive expansion against bounded
compiler work/storage/depth budgets. Each request either completes, returns a
structured failure, or ends with a resource diagnostic. No failure falls back
to ordinary application or leaves an executable unexpanded invocation.
Numeric budgets and host configuration are compiler policy, not source language
constants or a termination guarantee.

With equal source syntax and contexts, checked dependency closure, syntax
interface version, and semantic options, expansion is deterministic modulo
renaming fresh compiler identities and possible resource exhaustion. Fresh
identity numbers and host allocation order are not observable through the API.
Source order fixes expansion and diagnostic order. Alpha-renaming must preserve
every binder/use and checked access relationship; it cannot change visible
spelling, chosen declaration, or source location. Repeat-compilation tests
compare this equivalence rather than raw handle numbers.

These inputs also define invalidation: changing the matcher, transformer,
helper body or checked contract, definition/caller binding or syntax context,
retained origins, source input, interface version, or semantic options
invalidates an affected retained expansion. This does not require a persistent
cache in the first slice. A later cache must re-establish current-compilation
identities and origins rather than deserialize old handles as authority.

## Output admission and diagnostics

Every successful output parses as exactly one expression with no trailing
tokens, invalid group, missing node, or recovery node. It retains the original
source invocation and a generated syntax representation, not a replacement
source file. Nested invocations cross the same expansion boundary. Generated
syntax cannot forge a resolved type, selected implementation, builtin identity,
or validated Core fact.

The diagnostic classes remain distinct:

| Failure | Required cause and location |
| --- | --- |
| Invalid definition, matcher, or import | Definition/header error with its conflicting item or dependency route. No transformer runs. |
| Malformed invocation | First invalid capture or missing separator, invocation, and selected syntax definition. |
| Macro-authored rejection | Its message and selected input origins, plus the producing invocation/definition frame. |
| Evaluator, service, budget, or output failure | Underlying structured cause, invocation, definition, and construction/transformer origin where available. |
| Ordinary generated-program rejection | Original resolution/type/effect/etc. reason and facts, all causal input origins, and relevant expansion frames. |

Spliced argument failures prefer the original source location as primary.
Generated failures retain the introducing template or operation origin and the
invocation. Multi-input failures retain all relevant fragments: a branch
mismatch needs both branch origins, not one parent span. Nested expansion
frames remain ordered. Human output and locale-independent JSON preserve those
relationships under
[AD-0010](../../decisions/AD-0010-human-diagnostic-presentation-and-localization.md).
Macro-authored messages are source-authored text; compiler-owned reasons and
messages retain the normal localization contract.

For `if 42 then 1 else 2`, the ordinary error must point to `42` and retain the
Boolean expectation from the generated match. The compiler need not invent the
phrase “condition of if.” Such wording would need a separate declared role or
a justified macro-authored diagnostic. Provenance supplies causes, not new
typing facts or an inference of author responsibility.

The retained representation is inspectable in tests and tooling with contexts
distinguishing same-spelled names. A CLI expansion viewer or stepper is not a
completion prerequisite. Normal errors must be useful without one.

## Required acceptance evidence

[CP-0033](../../proposals/CP-0033-hygienic-expression-syntax.md) owns the
complete semantic evidence requirements. The pending M01–M14 delivery matrix
has moved to its owning
[TASK-0067 acceptance record](../../tasks/TASK-0067-expression-macros.md#acceptance-evidence).
The task retains the positive and negative cases, the real file-graph acceptance,
checkpoint obligations, and retained verification. No case is implemented or
accepted by this transfer.

## Delivery ownership

The prospective D0–D4 sequence is now the task-owned
[execution plan](../../plans/2026-11-05-expression-macros.md). It records the
producer/consumer agreements, source/header staging, private reference closure,
checked Ash host transfer and failure, shared public token vocabulary,
real interpreter/build consumers, integration ownership, checkpoints, and the
whole remaining delivery estimate. It has no independent semantic authority.

The accepted parser amendment in
[AD-0005](../../decisions/AD-0005-parser-architecture.md) admits one built-in
prefix mechanism parameterized by imported matcher data. Lexer separation,
shared precedence, token-complete recovery, and rejection at projection remain.
It admits no executable parser registry. The implementation remains pending.

No experiment is a prerequisite to the accepted design choices. A contradiction
or missing semantic rule returns to CP-0033. Persistent caches, an expansion UI,
declaration macros, typed compiler transformations, self-hosting, browser hosting,
and migrations that shrink the foundation remain separate work.
