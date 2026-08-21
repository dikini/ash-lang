# DN-0003: Parser Architecture

- ID: `DN-0003`
- Status: exploring
- Related: [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0005: Surface Function Definitions](DN-0005-surface-function-definitions.md), [DN-0015: Mini-Ash Phase](DN-0015-mini-ash-phase.md)

> This design note is informative. It does not accept a parser architecture or define Ash grammar.

## Intent

Choose a parser architecture that can grow with the language without repeatedly restructuring unrelated parser code. Keep the normative grammar independent of parser implementation structure.

EBNF is the likely notation for a future normative grammar, but neither the notation nor any Ash grammar is accepted by this note.

## Accepted implementation boundary

[AD-0005](../decisions/AD-0005-parser-architecture.md) accepts separate lexing,
event-producing grammar-shaped recursive descent, one explicit application and
infix precedence layer, token-complete error-bearing concrete syntax, and a
recovery-free surface-AST projection. It does not accept Ash grammar, layout, a
parser library, concrete event or tree types, incremental parsing, or trivia
policy. This note continues to explore those open implementation and grammar
pressures without overriding the accepted architecture.

## Constraints

- The specification defines accepted lexical structure, syntax, precedence, associativity, and ambiguity rules independently of parser code.
- Parser extension points are implementation details and do not appear in the language specification.
- Candidate architectures must be compared on grammar growth, precedence, ambiguity, diagnostics, error recovery, source spans, and tooling support.
- Current work must not choose surface syntax merely to fit a parser framework.

Current work need not support the full expected future language. It should use enough representative syntax pressure to expose structural weaknesses.

## Candidate directions

[AD-0005](../decisions/AD-0005-parser-architecture.md) selects the parser
organization. Remaining comparisons concern concrete event and tree
representations, recovery synchronization, trivia coverage, storage, and
libraries within that boundary. Research should compare their concrete
behavior rather than selecting a framework by reputation or adjectives. It
should reopen the accepted organization only when contrary evidence identifies
a named failure.

## Experiments

Use progressively richer provisional grammar and diagnostic cases from the
[Mini-Ash evaluation corpus](DN-0015-mini-ash-phase.md#corpus-strata). The corpus
is experimental input rather than accepted Ash syntax. Start with the
[first-stratum grammar and cases](DN-0016-first-mini-ash-corpus.md), including
the equational and inline operational definition pressure.

- express a small provisional grammar separately from each parser prototype;
- add an operator with precedence and associativity;
- add a nested construct without changing unrelated parser modules;
- preserve source spans through successful parses;
- compare specific Elm- and Rust-style diagnostics and recovery for malformed,
  incomplete, and ambiguous input;
- note how each candidate supports formatter or editor tooling without making that tooling a current requirement.

The provisional grammar exists only as experimental input. It must not be published as current Ash syntax.

## Open questions

- Which architecture makes grammar growth local and reviewable?
- How should precedence and ambiguity be represented and tested?
- What recovery behavior is useful for the first implementation?
- Which source representation best serves diagnostics and later tooling?
