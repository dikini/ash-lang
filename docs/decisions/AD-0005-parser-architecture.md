# AD-0005: Parser Architecture

- ID: `AD-0005`
- Status: accepted
- Related: [AD-0006](AD-0006-front-end-semantic-boundaries.md),
  [DN-0003](../design/DN-0003-parser-architecture.md),
  [DN-0016](../design/DN-0016-first-mini-ash-corpus.md),
  [first-stratum parser comparison](../design/mini-ash/first-stratum/comparisons/parser-architecture.md),
  [TASK-0067](../tasks/TASK-0067-expression-macros.md)

## Decision

Ash separates lexing from parsing. The parser uses grammar-shaped recursive
descent that emits events for an error-bearing, token-complete concrete syntax
representation. It is lossless with respect to the lexer token stream and the
source coverage required by the applicable grammar. A separate trivia decision
will determine whether that token stream covers every source byte.

A dedicated Pratt or precedence-climbing layer owns juxtaposed application and
infix precedence, associativity, and non-associativity. Definition, block,
pattern, type, and nested-expression parsers remain separate from that operator
layer.

One explicit parser-dialect assembly point lists the global-definition forms,
expression prefix forms, infix entries, pattern forms, and type forms available
to that dialect. Feature parsers own their local grammar and recovery behavior.
The assembly point remains closed over built-in parsing mechanisms.

For the expression-syntax transition in CP-0033, that assembly includes one
built-in loose expression-prefix mechanism parameterized by an immutable
imported matcher environment. The environment contains selected
syntax identities, local leading spellings, restricted matcher data, definition
origins, import routes, and ownership of their checked dependencies. It cannot
install a parser function, operator, precedence entry, or recovery callback.
The [grammar](../../spec/syntax.md#grammar) and
[syntax-expansion specification](../../spec/syntax-expansion.md) describe its
language forms retained on the milestone branch. QA confirmation remains
pending; Main integration is separate.

Fixed import-header discovery precedes body parsing. The loader discovers and
canonicalizes declared dependencies without executing transformers. The
compiler checks dependencies before supplying their selected syntax exports to
the importer body parser. Context-bearing generated syntax uses the matcher
environment retained by its identifiers. The parser recognizes invocations and
captures; the expansion phase executes transformers. A selected invocation
does not fall back to ordinary application after a parse failure.

The existing precedence owner handles operators and application. The new prefix
mechanism uses explicit enclosing expression boundaries and literal stop tokens;
it does not become an application primary or add another operator parser.
Protected expression fragments retain their parsed grouping without converting
syntax to text. All source and generated input retains token-complete recovery
information. Missing or error-bearing structure cannot become a capture,
transformer input, or projected surface input.

Parser events retain consumed tokens, delimiters, missing-token markers, error
nodes, and structured diagnostics. A separate projection produces the spanned
surface AST consumed by resolution. Projection fails while any missing or error
node remains, so recovery placeholders cannot reach static semantics.

The normative grammar remains independent of parser functions, event types,
precedence APIs, recovery mechanisms, and any implementation grammar.

## Context

The first corpus compared direct spanned-AST recursive descent,
event-producing recursive descent, parser combinators, and a generated parser.
It required two global function presentations, blocks, patterns, nested
functions, application by juxtaposition, three infix levels, right-associated
function arrows, non-associative equality, complete delimiter spans, and
specific recovery for `P-001` through `P-003`.

Direct AST construction was the smallest batch-parser baseline, but it needed a
parallel recovery structure or error variants and complete token coverage to
meet diagnostics and tooling pressure. That recreated a concrete syntax tree
without an explicit boundary.

Combinators could express local grammar, but the required commitment,
precedence, event, delimiter, missing-node, and synchronization contracts still
needed explicit architecture. A generated parser added a second implementation
grammar and custom tree and recovery actions before the provisional grammar was
large or stable enough to justify them.

Event-producing recursive descent kept grammar control explicit while
separating token-complete recovery data from the resolver's validated surface
input.

CP-0033 requires dependency-selected natural syntax before importer body parsing.
A fully static spelling list cannot represent those imports. Treating restricted
matchers as data for one built-in prefix mechanism preserves the existing parser
boundaries. Executable grammar callbacks would add parsing, recovery, and
execution contracts outside the accepted slice; printing expansions and
reparsing them would lose protected grouping and context. This amendment records
the architecture for TASK-0067; it does not create a broader grammar extension
API.

## Consequences

- Tokens carry exact source spans and preserve layout boundaries required by the
  applicable grammar.
- The error-bearing concrete representation may contain missing and error nodes;
  the resolver input may not.
- Application and infix grouping have one parser mechanism and one reviewable
  precedence table or equivalent data definition.
- Adding an operator changes its token support, feature parser, and dialect
  entry rather than unrelated declaration or nested-form parsers.
- Adding a nested construct changes its feature parser and the relevant closed
  dialect entry rather than the infix parser.
- Parser diagnostics carry structured reasons, primary and related spans,
  expected forms, and recovery context independently from rendering.
- The imported matcher environment has checked dependency provenance and remains
  owned for every source or generated parse that consumes it. Header discovery,
  matcher recognition, and transformer execution are separate operations.
- Formatter and editor tooling may reuse concrete syntax without making it
  language or semantic authority.
- This decision does not choose Ash grammar, layout, semicolons, multiline
  equations, a parser crate, a concrete-tree library, token storage,
  incremental reparsing, trivia policy, or final-expression file structure.

## Verification

Parser implementation and every grammar-changing task must show:

- successful parsing and complete spans for every applicable positive corpus
  case;
- precedence, associativity, non-associativity, grouping, and function-arrow
  tests required by the applicable accepted grammar, independent from static
  semantics;
- structured outcomes for every applicable accepted parser-diagnostic case,
  with the specified primary and related spans and no recovery-only cascades;
- rejection of concrete syntax containing recovery nodes at the surface-AST
  projection boundary;
- complete token and delimiter coverage needed by diagnostics and approved
  tooling;
- locality evidence for adding one operator and one nested construct;
- agreement between the implementation grammar and the applicable normative
  grammar without publishing parser extension points as Ash syntax.

TASK-0067 additionally verifies the data-defined prefix mechanism against
CP-0033's M01/M02/M07/M08 cases: checked imports reach the real body parser,
nested forms consume their own separators, protected fragments keep grouping,
and recovery-bearing structures are rejected before expansion. Existing valid
no-syntax inputs retain their parse and applicable diagnostic regression
evidence. The reviewed product checkpoint implements this extension;
TASK-0067 records its evidence and remaining integration work.
