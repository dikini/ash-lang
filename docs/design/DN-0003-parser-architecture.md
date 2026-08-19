# DN-0003: Parser Architecture

- ID: `DN-0003`
- Status: exploring
- Related: [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0005: Surface Function Definitions](DN-0005-surface-function-definitions.md)

> This design note is informative. It does not accept a parser architecture or define Ash grammar.

## Intent

Choose a parser architecture that can grow with the language without repeatedly restructuring unrelated parser code. Keep the normative grammar independent of parser implementation structure.

EBNF is the likely notation for a future normative grammar, but neither the notation nor any Ash grammar is accepted by this note.

## Constraints

- The specification defines accepted lexical structure, syntax, precedence, associativity, and ambiguity rules independently of parser code.
- Parser extension points are implementation details and do not appear in the language specification.
- Candidate architectures must be compared on grammar growth, precedence, ambiguity, diagnostics, error recovery, source spans, and tooling support.
- Current work must not choose surface syntax merely to fit a parser framework.

Current work need not support the full expected future language. It should use enough representative syntax pressure to expose structural weaknesses.

## Candidate directions

No concrete candidate is yet supported by repository evidence. Research should identify multiple parser organizations and compare their concrete behavior rather than selecting a framework by reputation or adjectives. No implementation language, parser framework, or parsing strategy is currently preferred.

## Experiments

- express a small provisional grammar separately from each parser prototype;
- add an operator with precedence and associativity;
- add a nested construct without changing unrelated parser modules;
- preserve source spans through successful parses;
- compare diagnostics and recovery for incomplete and ambiguous input;
- note how each candidate supports formatter or editor tooling without making that tooling a current requirement.

The provisional grammar exists only as experimental input. It must not be published as current Ash syntax.

## Open questions

- Which architecture makes grammar growth local and reviewable?
- How should precedence and ambiguity be represented and tested?
- What recovery behavior is useful for the first implementation?
- Which source representation best serves diagnostics and later tooling?
