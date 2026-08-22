# TASK-0010: Finish Mini-Ash

- ID: `TASK-0010`
- Status: active
- Related: [CP-0004: Rank-1 Polymorphism](../proposals/CP-0004-rank-1-polymorphism.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0020: Ash Dialect Milestones](../design/DN-0020-ash-dialect-milestones.md), [execution plan](../plans/2026-08-23-finish-mini-ash.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0004 is the accepted transition authority. Current `spec/` remains
  normative until implementation, tests, and specification changes merge.
- Work runs on `feature/rank-1-polymorphism` in
  `.worktrees/rank-1-polymorphism`.
- Intermediate commits are unsigned. Integration requires review and explicit
  confirmation.
- Behavioral changes follow witnessed red-green-refactor cycles.

## Work

Execute the linked plan to add the complete corpus, parameterized nominal
types, kinded rank-1 checking, conservative local generalization, explicit Core
polymorphism, runtime erasure, specification changes, retained evidence, and
the final Mini-Ash simplification audit.

## Progress

- The user approved function-only local generalization, implicit source
  instantiation, explicit Core type operations, `Type`-only declaration
  parameters, and full milestone closure.
- CP-0004 records the accepted transition and evidence requirements.
- The worktree starts from `main` at `9e7a5e0`. `cargo build` and
  `cargo test --all-targets` passed before changes.
- Product implementation has not started.

## Verification

Focused checks are recorded in the execution plan. Completion requires:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo xtask verify
```

Manual review covers Markdown, links, authority, formal notation, changed Core
consumers, type-work accounting, ownership and release boundaries, and the
absence of excluded higher-rank, higher-kinded, module, effect, or runtime-type
semantics.

## Discoveries

None yet. Record implementation findings here and distill transferable results
into retained evidence.

## Deviations

None.
