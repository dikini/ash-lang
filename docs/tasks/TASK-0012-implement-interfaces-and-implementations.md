# TASK-0012: Implement Interfaces and Implementations

- ID: `TASK-0012`
- Status: active
- Related: [CP-0006: Interfaces and Implementations](../proposals/CP-0006-interfaces-and-implementations.md), [DN-0023: Interfaces and Implementations](../design/DN-0023-interfaces-and-implementations.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), and the [execution plan](../plans/2026-08-24-implement-interfaces-and-implementations.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0006 is accepted transition authority. Current `spec/` remains normative
  until implementation, tests, and specification changes are committed together
  on this feature branch.
- Work runs on `feature/modular-ash` in `.worktrees/modular-ash` and remains
  unmerged unless the user later requests integration.
- The implemented passive-module boundary remains intact: canonical module
  identity, direct imports, body-free checked summaries, opacity, hidden
  nominal identity, dependency-ordered Core groups, and entry `main` are inputs
  to this work rather than interface semantics to redesign locally.
- Behavioral changes use witnessed red-green-refactor cycles. Production Rust
  follows the project lint configuration and the selected Rust ownership,
  error, API, type-safety, testing, and documentation guidance.
- Interface selection must remain structurally attached through checking and
  linking. A span-keyed side table or repeated selection during final lowering
  does not satisfy CP-0006.
- Intermediate commits may contain a deliberately incomplete transition but
  must state their bounded checkpoint and keep their focused tests green.

## Work

Execute the linked plan to:

- parse and project method-only interfaces, trailing `where` requirements, and
  implementation declarations;
- allocate stable qualified interface, method, impl, impl-method, requirement,
  and hidden binder identities;
- extend checked schemes and body-free summaries without changing ordinary
  type equality or turning summaries into source module signatures;
- check interface and impl headers, visibility, orphan ownership, structural
  termination, exact method membership, and scoped overlap;
- select abstract, exact-rigid self, concrete, and generic prerequisite evidence
  once and retain it on the checked occurrence;
- validate linked evidence identities, availability, substitutions, method
  order, scope, type, and provenance before Core synthesis;
- lower evidence to existing type abstractions, ordinary function binders,
  applications, and module recursive groups without a new Core or evaluator
  feature;
- close diagnostics, graph-wide interface-and-constraint accounting,
  deterministic failures, deep worklists, and small-stack destruction;
- update the corpus, normative specification, tool docs, retained evidence,
  proposal/task indexes, and trajectory; and
- leave associated types, specialization, first-class dictionaries, runtime
  lookup, module signatures, effects, and the later core-versus-library audit
  outside this implementation task.

## Progress

- CP-0006 converged through independent syntax, semantics, and implementation-
  boundary reviews and is accepted.
- The worktree baseline is unsigned commit `ca79328` on
  `feature/modular-ash`.
- `cargo xtask verify` passes before implementation. The baseline contains 645
  passing tests across the library, executable, integration targets, and
  `xtask`, with no failure.
- Markdown lint with existing line-length exceptions, relative-link checks, and
  `git diff --check` pass for the accepted design and proposal artifacts.
- The implementation plan records the intended red-green checkpoints. No
  production interface implementation has started.

## Verification

Focused commands and witnessed RED/GREEN outcomes are recorded in the execution
plan. Completion requires:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo clippy --locked --all-targets -- -D warnings
cargo xtask verify
```

Manual review covers every CP-0006 evidence requirement, Markdown, relative
links, artifact authority, formal notation, reason codes, source occurrence
ownership, summary isolation, direct-only impl availability, graph-wide budget
lifetime, all changed Core consumers, and the absence of associated types,
runtime lookup, interface Core nodes, span-keyed selection, or a new evaluator
dispatch rule.

## Discoveries

None yet.

## Deviations

None.
