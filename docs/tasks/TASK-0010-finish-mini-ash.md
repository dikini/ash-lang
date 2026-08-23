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
- Checkpoints `279da15`, `423baa3`, `959533b`, and `8195e6f` implement syntax,
  resolution and inference, explicit Core operations and erasure, and cumulative
  type-work accounting.
- The normative specification, executable tool example,
  [rank-1 integration evidence](../design/mini-ash/rank-1-polymorphism/evidence.md),
  and [Mini-Ash closure report](../design/mini-ash/closure.md) are prepared for
  the final verification and review checkpoint.

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

At the review checkpoint, `cargo xtask verify` passes all format, metadata,
build, Clippy, test, and rustdoc checks. Markdown lint passes for every changed
document with the repository's existing long-line exceptions. New and changed
relative links resolve, and the new `sequent` rules have matching prose.

## Discoveries

- New type payloads increased elaboration frame size enough to expose a
  pre-existing host-stack dependency in deep structured matches. An explicit
  match task stack restored the 256 KiB boundary.
- Local generalization must exclude inference variables free in the incoming
  environment; checking only the initializer's syntax is insufficient.
- Recursive global self-occurrences need the definition's rigid arguments,
  while ordinary occurrences need fresh instantiation.
- Parameterized coverage reuses the existing usefulness relation after
  substituting owner arguments into constructor payloads.
- The retained 10,000-member cyclic group requires more than 262,144 cumulative
  type-work units. A 327,680-unit limit admits it while oversized direct Core
  tests still prove structured resource failure.
- Full verification found and corrected two compatibility regressions: nested
  blocks no longer receive the direct-anonymous-function generalization
  privilege, and zonking preserves precise application-result provenance when
  its type shape is unchanged.
- Boxing the two structural types inside rare mismatch errors keeps the public
  diagnostic API intact while restoring the denied `result_large_err` lint.
- Recursive rigidity belongs to the definition currently being checked. Other
  global schemes remain ordinary occurrences and instantiate freshly.
- Type rebuilding must preflight the expanded zonked or substituted result.
  Charging only its compact input permits multiplicative retained work before
  the resource boundary can respond.
- Core registry closure includes nominal parameter metadata and requires every
  constructor payload variable to belong to its owner. Constructor payloads
  remain monotypes.
- Stable Core type-variable identities have one abstraction definition site;
  two distinct abstraction nodes cannot reuse the same identity.
- Resource accounting includes temporary retained replacement maps, coverage
  rows and arms, context entries, and provenance handles. Wide zonking and
  occurs-check traversal retain constant pending fan-out.
- Successful whole-program inference retains its zonked result before the
  driver constructs source-facing type output; later Core rewriting is not the
  owner of that public type.
- Synthesized tuple-payload wrappers and rebuilt function-shaped provenance are
  separate retained type metadata. Both require cumulative charges in addition
  to the structural types that caused their construction.

The retained integration and closure reports contain the transferable results
and boundary audit.

## Deviations

None.
