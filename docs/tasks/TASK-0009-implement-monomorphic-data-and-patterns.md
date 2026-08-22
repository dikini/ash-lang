# TASK-0009: Implement Monomorphic Data and Patterns

- ID: `TASK-0009`
- Status: active
- Related: [CP-0003: Monomorphic Data and Patterns](../proposals/CP-0003-monomorphic-data-and-patterns.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0007: Data and Pattern Typing](../design/DN-0007-data-and-pattern-typing.md), [DN-0019: Primitive Feature Composition](../design/DN-0019-primitive-feature-composition.md), [execution plan](../plans/2026-08-22-monomorphic-data-and-patterns.md), [shared-pipeline remediation design](../plans/2026-08-22-data-and-patterns-shared-pipeline-design.md)

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
- The positive and rejection corpus covers finite trees, tuple domains,
  higher-order constructors, nested patterns, shared coverage, guarded cycles,
  mixed recursive groups, transforms, malformed registries, and exact syntax
  spans.
- The implementation carries nominal and constructor registries through a
  structured data-and-pattern Core boundary, independently rechecks it, and
  evaluates it with a per-run numeric-location heap.
- Normative and tool documentation has executable examples. The retained
  integration report is linked from DN-0007 and DN-0019.
- A 10,000-member cycle evaluates, renders, and drops on a 256 KiB host stack.
- Unsigned checkpoints `d2e84c6` through `8cf8b4e` retain authorization and
  the first candidate implementation. Review found that its private parser,
  Core wrapper, evaluator, and source-text routing violated the retained
  compiler boundaries.
- Unsigned checkpoints `23537c2` and `b6a683d` record the approved remediation
  design and execution plan. Checkpoints `e18620a`, `c3f7962`, and `8c1c6af`
  migrate syntax, resolution, typed Core, validation, heap evaluation, and all
  source programs into the retained pipeline, then delete the parallel path.
- Checkpoint `ac840eb` adds strict tuple-construction trace evidence and literal
  folding through structured data, makes usefulness iterative and memoized,
  and closes the project lint findings exposed by the retained forms.
- The final remediation gate passes `cargo fmt --all --check`,
  `cargo check --locked --all-targets`, `cargo test --locked --all-targets`,
  and `cargo xtask verify`, including the 10,000-member small-stack case.
- Markdown lint passes for every changed document with line-length and repeated
  execution-step headings disabled. All changed relative links and anchors
  resolve. Authority, formal notation, exclusions, and the requirement mapping
  have been reviewed against CP-0003 and the normative specification.

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

The usefulness relation needs an explicit empty-matrix base case. Without it,
cycle detection incorrectly labels a constructor pattern over a recursive
single-constructor type redundant. The retained corpus now fixes that case.

Active-path rendering must remove a completed location so shared acyclic values
repeat structurally while true cycles terminate. An explicit rendering stack
also makes long heap observations independent of the Rust call stack.

The registry accessor, observation heap, and type-family mutation probes were
compiler-discoverable and were reverted. The retained evidence report records
the exact results.

## Deviations

The first candidate used a feature-owned parser, Core wrapper, evaluator, and
driver-level source-text switch. Review rejected that deviation for product
integration. The approved
[remediation design](../plans/2026-08-22-data-and-patterns-shared-pipeline-design.md)
migrated the behavior into the retained CST, resolution, typed Core,
validation, transforms, and evaluator-machine boundaries. Commit `8c1c6af`
deletes the parallel module and its driver, failure, and value variants. No
known architecture deviation remains for the review candidate.
