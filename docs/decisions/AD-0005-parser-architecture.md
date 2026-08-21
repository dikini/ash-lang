# AD-0005: Parser Architecture

- ID: `AD-0005`
- Status: accepted
- Related: [AD-0006: Front-End Semantic Boundaries](AD-0006-front-end-semantic-boundaries.md), [DN-0003: Parser Architecture](../design/DN-0003-parser-architecture.md), [DN-0016: First Mini-Ash Corpus Stratum](../design/DN-0016-first-mini-ash-corpus.md), [first-stratum parser comparison](../design/mini-ash/first-stratum/comparisons/parser-architecture.md)

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
to that dialect. Feature parsers own their local grammar and recovery behavior;
the assembly point remains closed so the implementation can review the exact
accepted forms.

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
