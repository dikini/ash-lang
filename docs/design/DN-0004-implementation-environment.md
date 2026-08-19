# DN-0004: Implementation Environment

- ID: `DN-0004`
- Status: exploring
- Related: [DN-0002: Core Representation](DN-0002-core-representation.md), [DN-0003: Parser Architecture](DN-0003-parser-architecture.md)

> This design note is informative. It does not select an implementation language, build system, package manager, or toolchain.

## Question

Which implementation environment best supports the first Ash compiler work and the experiments needed to choose parser and Core architecture?

This choice must converge into an architectural decision before implementation tasks depend on it. Bootstrap work must not select an environment implicitly.

## Constraints

Candidate environments must be evaluated against concrete project work:

- typed, inspectable compiler representations;
- explicit continuation data and reliable traversal and rewriting experiments;
- parser experiments involving precedence, diagnostics, recovery, and source spans;
- checks for IR invariants after transformations;
- a small, reproducible contributor setup.

No repository evidence currently prefers a language, build system, package manager, parser framework, CI stack, formatter, or linter.

## Evidence and experiments

After the Core and parser investigations identify representative operations, compare a small set of candidate environments by implementing equivalent bounded probes. Record how each candidate expresses invariants, transformations, parser organization, diagnostics, tests, and project setup.

Choose based on those results and documented tradeoffs, not on familiarity or broad claims about a tool's qualities.

## Open questions

- Which host type-system properties materially reduce mistakes in typed IR work?
- Which graph and tree operations must the environment express directly?
- What is the smallest repeatable setup for contributors and automated checks?
- Which constraints are essential for the first implementation, and which can wait?
