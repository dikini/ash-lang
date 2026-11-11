# Syntax Expansion

Expression and declaration syntax let a module publish a matcher and either a
template or a checked Ash transformer. An importer activates a syntax name
explicitly. Expression expansion produces an ordinary expression; declaration
expansion produces ordinary module declarations. Both cross the usual name
resolution, checking, elaboration, linking, and independent Core validation
boundaries. A transformer receives syntax, not inferred types, selected
implementations, or Core.

## Definitions and imports

The [surface grammar](syntax.md#grammar) admits public module-level syntax
declarations and targeted syntax import items. For example:

```ash
pub syntax if $condition:expr then $yes:expr else $no:expr => {
    match $condition {
        true => $yes
        false => $no
    }
}
```

The braces form the resulting block expression. A procedural declaration uses
`=> using transformer`, where `transformer` is an ordinary global in the
defining module. Each syntax name begins with a lowercase letter and is not a
reserved word. A matcher occupies one logical line and contains literal tokens
and uniquely named `expr` or `ident` captures. Matchers
contain at least one capture, end in an expression capture, and place a
literal between adjacent captures. Matchers have no repetition, alternatives,
optional items, or parser callbacks. A literal is matched by token kind and
spelling. Groups, logical line ends, `$`, and `=>` are not matcher literals.

An import such as `import forms (syntax if as choose)` activates the selected
module's own public export under `choose`. A complete module import does not
activate syntax. Duplicate local syntax names, missing exports, local or
private syntax declarations, syntax re-exports, and use of a module's own
syntax in that module are rejected. A syntax-defining module may use forms
imported from its acyclic dependencies. The local syntax name is reserved for
unqualified source-authored term binders and references in its importing
module; a rename can avoid a conflict. Qualified members are unaffected.

Dependency headers are discovered and checked before the importing module's
body is parsed with its selected syntax. Header discovery does not execute a
transformer or permit expansion to add an import. A template is checked for
syntactic validity at definition time with category-correct capture
placeholders, without resolving its free names. When expanded, a literal free
reference resolves in the defining module's checked environment. An
unresolved or inaccessible name fails then; an unused template does not fail
for that name. A caller's same-spelled binding or import cannot supply it.

## Matching and expansion

A non-final expression capture stops at its next matcher literal at the
current expression level. Complete nested invocations consume their own
separators first. An identifier capture consumes one identifier and requires
its following literal. The final expression capture extends to the enclosing
expression boundary. Invocations have the loose prefix precedence described
in [syntax](syntax.md#precedence-and-associativity); parenthesize one used as
an application or infix operand. Once a selected syntax name is encountered,
malformed input is a syntax failure, not an ordinary-application fallback.

Templates and procedures use ordered syntax nodes, balanced groups, and
protected expression fragments. Splicing a captured expression preserves its
grammatical boundary: inserting `a + b` after a function is equivalent to
passing `(a + b)`. A fragment is not a lexical scope. The explicit
`expression_syntax` operation exposes a fragment's contents without that outer
boundary, preserving nested fragments, contexts, and origins.

Expansion is outermost first. Completed subtrees are visited in source order;
a captured nested invocation runs only when its occurrence survives in the
output. Each occurrence of a copied fragment is resolved separately, so its
local binders and nominal or resource identities are distinct while its
internal uses remain connected. Free caller references keep their context.
Expanding a copy does not change another copy. Runtime evaluation follows the
resulting ordinary program; duplication does not imply single evaluation.

## Imported declaration syntax

An imported declaration syntax is selected in a module declaration position.
Its contextual header names the declaration form:

```ash
pub syntax declaration: (ones) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = 1
    )+
}
```

Declaration matchers support `ident`, `expr`, `type`, `pattern`, and
`declaration` captures. An identifier consumes one name. The expression,
type, and pattern captures retain their ordinary grammatical boundaries. A
declaration capture is enclosed in braces and must contain exactly one complete
ordinary module declaration, including its signature and equations when those
form one declaration. Its braces are not part of the captured declaration.
The capture retains the caller's contexts and origins until it is consumed as
one module declaration. It cannot be used as an expression, type, pattern, or
local declaration.

Matchers can contain balanced groups and nested `*` or `+` repetitions with an
optional single-token separator. Captures retain their source order and nested
shape. A variable-length capture stops at the next applicable literal,
repetition separator, group delimiter, or invocation boundary at its own
syntactic level. Adjacent captures and ambiguous repetition boundaries are
rejected at definition admission. A one-or-more matcher requires an iteration;
a separator requires another iteration after it.

A declaration template can repeat its output with the same operators and
optional separator. A repeated capture drives its corresponding template
repetition, and multiple drivers at that level must have equal lengths. Nested
repetitions select their current outer elements, so inner lengths may differ
between outer iterations. A repetition without a driver is rejected when its
definition is admitted; unequal live drivers reject the invocation. Failure
publishes no partial expansion. Completed output is handed to the existing
module declaration parser without re-lexing generated text.

Structured repetition currently applies to declarative declaration templates.
Generator clauses, per-iteration escapes, and the remaining procedural repeated
capture paths are still under development. See the
[declaration grammar](../docs/design/macros/declaration-grammar.md) for the
accepted wider design.

## Quotation and template escapes

A checked ordinary helper used during syntax expansion can construct an
`ExpressionFragment` with `syntax { expression }`. Its braces delimit the
quoted expression. Inside that quote, `$name` inserts the fragment held by an
ordinary Ash variable, and `${ expression }` evaluates an inner expression
that produces a fragment. These expressions use ordinary lexical scope and
ordinary checking; a primitive value is not implicitly converted to syntax.
A quotation requires an active compile-time syntax host when it is evaluated.
Reaching one during ordinary runtime execution fails rather than publishing an
internal fragment representation.

A declaration template can contain `${ expression }` or a multiline escaped
block. The escaped code runs during expansion and its `ExpressionFragment`
result is inserted as protected syntax for ordinary admission and checking.
An escaped expression fragment in a type position is rejected by syntax
admission. A procedural expression transformer can return the token and group
view of a quoted capture for reparsing; the tokens retain their syntax contexts
and origins. Direct forwarding of a protected quoted expression remains under
development. The currently connected escape path covers escaped code that does
not read matcher captures. Capture reads in escaped code, per-iteration escapes,
and generators in [CP-0034](../docs/proposals/CP-0034-top-level-declaration-macros.md)
remain under development.

## Names and hygiene

Names retain compiler-issued lexical and syntax contexts as well as spelling
and diagnostic origins. The ordinary lexical scope of each binding form is
established at its actual position in the expanded expression. A sequential
`let` initializer precedes its binder's scope; recursive members share their
simultaneous scope. Function parameters, match patterns, local nominals,
resources, regions, and continuation capabilities use their ordinary scope
rules. Captured identifiers and expressions keep their contexts. Each
expansion gives its literal introduced identifiers the selected definition
context and one shared fresh introduction. An introduced binder does not
capture an unrelated same-spelled caller reference. A captured identifier used
as a binder can bind same-context captured references in its proper body.

Syntax lookup uses the leading identifier's retained syntax context. A
captured invocation retains the caller's imports; a literal invocation in a
template retains the defining module's imports. A same-spelled caller syntax
cannot redirect it. `fresh_identifier` creates a distinct private context,
`definition_identifier` chooses the definition context, and
`caller_identifier` deliberately chooses the invocation context. Spelling or
an origin alone cannot create any of those contexts.

Definition-context lookup uses the defining module's actual lexical access.
Published syntax may use that module's private helper or its own opaque
constructor, without importing that name into the caller. Neither the owner
nor the caller gains a dependency's unexported member or withheld opaque
constructor. A captured caller name retains caller access. Qualified lookup
first resolves the alias in its own context, then selects the member through
that module's public exports. Existing identities survive targeted renames and
facades. See [visibility and opacity](name-resolution.md#public-private-and-opaque-declarations).

A generated method reference retains its selected method identity, but does
not import the defining module's implementation evidence into the caller.
Ordinary caller and lexical evidence selection applies. Handler and
continuation capabilities likewise follow the actual expanded structure;
spelling and origins do not install a capability.

## Canonical syntax interface

`@builtin.compiler.syntax` is a compiler-owned module. It exports opaque
`Token`, `Identifier`, `ExpressionFragment`, `Input`, `Origin`, and
`ParseFailure` types. Their hidden constructors are not available to source.
The public structural types include these declarations:

```text
pub type Syntax = Syntax(Nodes)
pub type Nodes = NoNodes
    | MoreNodes(Node, Nodes)
pub type Node = TokenNode(Token, Origin)
    | IdentifierNode(Identifier, Origin)
    | GroupNode(Delimiter, Syntax, Origin)
    | ExpressionNode(ExpressionFragment, Origin)
pub type Delimiter = Parentheses
    | Braces
pub type Origins = NoOrigins
    | MoreOrigins(Origin, Origins)
pub type Capture = ExpressionCapture(ExpressionFragment)
    | IdentifierCapture(Identifier, Origin)
pub type CaptureResult = Captured(Capture)
    | MissingCapture
pub type OriginsResult = Combined(Origin)
    | MissingOrigins
pub type IdentifierResult = MadeIdentifier(Identifier)
    | InvalidIdentifier
pub type TokenResult = MadeToken(Token)
    | InvalidToken
pub type ParseResult = Parsed(ExpressionFragment)
    | ParseRejected(ParseFailure)
pub type MacroDiagnostic = MacroDiagnostic(String, Origin, Origins)
    | SyntaxDiagnostic(ParseFailure)
pub type MacroResult = Expanded(Syntax)
    | Rejected(MacroDiagnostic)
```

The closed `TokenKind` family and its spelling rules are listed in
[lexical structure](lexical-structure.md#public-token-kinds). The module's
canonical `Ops` effect declares the following operations, and its ordinary
functions of the same names request them. Each function has the shown latent
row together with the current implicit default-allocation requirement.

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

`capture` indexes captures in matcher order. A negative, unrepresentable, or
out-of-range index returns `MissingCapture`. `make_token` checks the token
kind and exact spelling; it cannot construct an identifier or an unbalanced
group. Identifier constructors check the spelling and return
`InvalidIdentifier` when it is not one identifier. `combine_origins` requires
a nonempty ordered input list and retains the current expansion frame; the
empty list returns `MissingOrigins`.

`parse_expression` accepts exactly one expression and preserves its contexts
and protected fragments. It does not resolve names, expand a nested
invocation, or run another transformer. A failed parse returns a
`ParseFailure`; returning it in `SyntaxDiagnostic` retains its structured
cause. Each `Input` and other opaque handle belongs to its issuing invocation.
Numbers, strings, source spans, and origins cannot forge one; a stale or
foreign handle is rejected at the host boundary.

## Transformer execution

A procedural transformer is an unconstrained, monomorphic global of its
defining module. Its actual type is `Input -> MacroResult` with a closed
latent row containing only default allocation and optionally the canonical
`Ops` instance. The check inspects that type; it does not add effect
subtyping. The defining module needs no source `main` for this purpose.

The compiler links the already checked transformer and its helper closure into
a compile-time entry and independently validates that new program. An
unchanged validated entry may be reused within the compilation; a changed
linked program is validated again. Each invocation receives fresh host input,
captures, contexts, and service state. The host provides default allocation
and syntax services, not native callbacks, network, filesystem, clock, target
queries, or ambient compiler mutation.

The complete output is transferred to compiler-owned storage before the
invocation's evaluation storage is released. Every exit disposes its owned
machine and output storage. Rejection, evaluator or service failure, invalid
output, or resource exhaustion publishes no partial expansion. A disposal
refusal records incomplete teardown without replacing the primary failure;
resource exhaustion does not guarantee execution of source cleanup. Transformer
steps, service work, output size, and recursive expansion use bounded compiler
work, storage, and depth policy; the numeric limits are not source constants.
The generated runtime program does not require a syntax-service interpreter.

## Output and diagnostics

Successful output must parse as exactly one expression without trailing input,
missing structure, invalid groups, or recovery nodes. Nested invocations use
the same expansion boundary. Resulting expressions receive the ordinary
type, evidence, effect, scope, and Core checks; generated syntax supplies no
validated semantic fact by itself.

Compiler diagnostics retain their ordinary structured reason and facts,
source and construction causes, and relevant invocation and definition
frames. A macro-authored rejection retains its source-authored message and
selected origins. A generated program's ordinary failure remains an ordinary
resolution, type, effect, or other checking failure. Human and JSON output use
the existing diagnostic presentation and localization rules; provenance does
not invent a DSL-specific role from a source span.
