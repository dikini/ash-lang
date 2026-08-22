# TASK-0009: Implement Monomorphic Data and Patterns

- ID: `TASK-0009`
- Status: active
- Related: [CP-0003: Monomorphic Data and Patterns](../proposals/CP-0003-monomorphic-data-and-patterns.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0007: Data and Pattern Typing](../design/DN-0007-data-and-pattern-typing.md), [DN-0019: Primitive Feature Composition](../design/DN-0019-primitive-feature-composition.md), [execution plan](../plans/2026-08-22-monomorphic-data-and-patterns.md), [shared-pipeline remediation design](../plans/2026-08-22-data-and-patterns-shared-pipeline-design.md), [match-context correction design](../plans/2026-08-22-match-context-and-semantics-review-design.md), [match-context correction plan](../plans/2026-08-22-match-context-and-semantics-review.md)

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
- Review checkpoint `79af325` bounds parser, Core-pattern, usefulness, and
  registry resources; authenticates registry identities and source order;
  makes registry rejection and recursive-root validation stack safe; restores
  complete evaluator transition ownership; and adds full-pipeline depth,
  wide-constructor, match-trace, and structured-diagnostic evidence.
- Checkpoint `ca3ae75` records the corresponding warning-free Clippy gate.
- Review checkpoint `77ca07b` charges every nested pattern cell during
  usefulness shaping and centralizes registry-aware type rendering for source
  diagnostics while retaining nominal identities for equality and structured
  mismatch inspection.
- Review plan checkpoint `807329d` records the approved correction for
  contextual match typing and normative formal consistency. Checkpoint
  `46df1aa` passes an expected result type and diagnostic cause to every arm of
  a checked match without changing match synthesis or Core.
- Specification checkpoint `b157e14` adds typed-pattern and singleton-coverage
  premises to function and local-binding rules, separates match synthesis from
  checking, gives guarded recursive initialization explicit entry and storage
  transitions, and describes integer and closure bindings as direct values.
- Follow-up checkpoint `d349b0c` makes recursive allocation return the data
  binder-to-location map separately from its source-ordered initializer work,
  so the formal environment extension retains the identities used by lookup.
  Checkpoint `a141d5c` directly tests contextual diagnostic-cause propagation
  and each source-ordered initializer-entry and alias-storage continuation.
- Review checkpoint `5eb0cdb` retains the completed evaluation heap for scalar,
  structural, and closure results and transfers the same shared heap into
  pipeline observations. It adds direct closure-capture ownership regressions,
  gives operational globals the accepted pattern and singleton-exhaustiveness
  premises, and removes obsolete function-only recursion and binder-only
  equation wording from normative and Rust documentation.
- Review checkpoint `cff6fb5` replaces the quadratic reverse constructor-owner
  scan with direct lookup at the constructor identity index. A focused unit
  test fixes the indexed invariant, and a 10,000-constructor full-validation
  regression completes in 0.06 seconds on the retained evidence environment.
- Review checkpoint `c25dac3` removes obsolete public parser reasons and text
  that still described tuples, matches, multiple parameters, and multiple
  equation patterns as unavailable. An exhaustive public-reason regression
  keeps that diagnostic contract aligned with the retained grammar.
- Review checkpoint `8085a1f` charges copied tuple types and specialized
  pattern, type, state, and witness cells before allocation. Shared immutable
  usefulness states replace complete state clones, and a 100,000-field
  full-source tuple regression reaches structured coverage resource exhaustion.
- Fresh post-review `cargo test --all-targets` and `cargo xtask verify` runs
  pass, including the 10,000-member small-stack cycle and all new depth and
  resource regressions. Changed Markdown passes with only the project-approved
  line-length and repeated-heading rules disabled.
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
