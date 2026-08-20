# First Mini-Ash corpus stratum

> This evidence package is informative and governed by
> [DN-0016](../../DN-0016-first-mini-ash-corpus.md). Its programs, grammar,
> judgments, rules, and representations are provisional. They do not define
> current Ash or accept an architecture.

The first stratum combines primitive values, variables, immutable bindings,
monomorphic functions, and applications. It supplies shared evidence for
parser, Core, typechecker, evaluator, transformation, and diagnostic
comparisons.

## Evidence slices

- [Programs](programs.md) define stable case IDs and expected user-visible
  outcomes.
- [Grammar](grammar.md) gives one provisional syntax input for parser research.
- [Typing](typing.md) gives provisional declarative judgments and case outcomes.
- [Dynamics](dynamics.md) gives provisional small-step rules and traces.
- [Diagnostics](diagnostics.md) gives structured failure and rendering criteria.
- [Representations](representations.md) gives stage contracts and candidate
  pressure.

## Case identity

Case IDs remain stable within this evidence package:

- `V-NNN` identifies a valid program;
- `P-NNN` identifies rejected parser input;
- `R-NNN` identifies a resolution failure;
- `T-NNN` identifies a typing failure;
- `I-NNN` identifies a malformed internal representation.
- `X-NNN` identifies a non-gating cross-stratum pressure case.

Other documents refer to these IDs rather than copying whole examples. A later
proposal may adopt a case as evidence, but that proposal must define its own
normative expectation.

## Shared provisional choices

The initial comparison input uses `Int`, `Bool`, and `Unit`; immutable global
and local bindings; unary first-class functions; application expressions; and
integer `+`, `*`, and `==` operations. Evaluation is strict and left-to-right.
A source file contains zero or more explicitly typed global definitions
followed by one result expression. Equational and inline operational
definitions begin from DN-0005. Equivalent cases may elaborate to the same or
similar callable Core, while clause structure, explicit match structure, and
presentation provenance remain observable.

These choices expose the first comparison questions. They remain open to
revision when a candidate or case supplies contrary evidence.

The `X-NNN` cases add only Boolean patterns, an explicit Boolean match, and one
product-domain grouping example. They make the equational/operational
distinction observable without placing general patterns, pattern matching, or
product data in the first retained semantic increment.

## Review gate

Before any component probe treats the package as input, review must confirm that
each referenced case has compatible syntax, scope, type, reduction, result or
rejection, source spans, and diagnostic expectations. A disagreement is a
corpus defect, not permission for a prototype to choose semantics locally.
