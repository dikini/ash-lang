# TASK-0009: Implement Monomorphic Data and Patterns

- ID: `TASK-0009`
- Status: active
- Related: [CP-0003: Monomorphic Data and Patterns](../proposals/CP-0003-monomorphic-data-and-patterns.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0007: Data and Pattern Typing](../design/DN-0007-data-and-pattern-typing.md), [DN-0019: Primitive Feature Composition](../design/DN-0019-primitive-feature-composition.md), [execution plan](../plans/2026-08-22-monomorphic-data-and-patterns.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0003 is the accepted transition authority. Current `spec/` remains
  normative until implementation, tests, and specification changes merge.
- AD-0005 through AD-0008 govern parser recovery, front-end rule boundaries,
  typed Core validation, transforms, and the explicit evaluator.
- Work runs on `feature/data-and-adts` in `.worktrees/data-and-adts`.
- Intermediate commits are unsigned. Integration requires review, explicit
  confirmation, retirement of temporary transition artifacts, fresh
  verification, and a GPG-signed merge commit.
- Behavioral work follows witnessed red-green-refactor cycles.

## Work

Execute the linked plan to add the complete corpus first, then deliver resolved
nominal identities and registries, tuples and finite constructors, typed
patterns and usefulness, guarded cyclic data, transforms, documentation, and
retained integration evidence.

## Progress

- The user supplied and authorized the combined semantic increment.
- CP-0003 records the accepted transition and evidence requirements.
- The worktree starts from `main` at `4d5ce64`. `cargo build` and `cargo test`
  passed before changes.
- Product implementation has not started.

## Verification

Focused commands are recorded in the execution plan. Completion requires:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo xtask verify
```

Manual review covers Markdown, links and anchors, authority boundaries, formal
notation, the requirement audit, changed Core consumers, heap ownership, and
the absence of unintended polymorphism, records, modules, pattern compilation,
or general laziness.

## Discoveries

None yet. Record implementation findings here and distill transferable evidence
into the retained report and linked design notes.

## Deviations

None.
