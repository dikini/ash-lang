# TASK-0035: Resource analysis relevance and algebraic fusion

- ID: `TASK-0035`
- Status: active
- Related: [DN-0036](../design/DN-0036-foreign-library-and-memory-provider-experiments.md), [AD-0007](../decisions/AD-0007-typed-core-dialects.md), [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This task organizes a bounded DN-0036 experiment. It defines no Ash semantics
> and accepts no general compiler architecture.

## Dependencies

The user authorized planning and execution on 2026-10-07 after selecting two
complementary directions: establish relevance before generating analysis work,
and simplify typed pipeline compositions through algebraic equivalences.
The starting integration checkpoint is `43248835a99b2d6061fafd41742778b62085eac0`.
Its full verification is recorded in Common receipt 259. The separate SQLite
worktree supplies the coherent native/library snapshot and original programs.

The user assigned implementation to this task, with Common coordinating shared
changes, Cargo windows and integration. Work stays in
`.worktree/algebraic-resource-analysis`, on `codex/algebraic-resource-analysis`.
Common granted the first F-2 slice: lexical capture collection and an internal
structural-product producer in `capture.rs`, abstract-capture replay and the
collector portions of Function, TypeAbstraction and clause construction in
`capture/value.rs`. Existing metadata preparation stays unchanged. Contexts,
slots, queues, runtime transfers, control and validation remain Common-owned.
The starting checkpoint is historical; rebase on the next verified integration
checkpoint before compiled comparison.

## Work

Execute the [analysis plan](../design/provider-experiments/analysis-plan.md):

1. Describe the existing pipeline using typed carriers, producers, consumers,
   demand dimensions and completion boundaries.
2. Separate demonstrated irrelevant work, unresolved relevance and repeated
   work. Bind each conclusion to source and completed evidence.
3. State candidate equivalences, their preconditions and counterexamples.
4. Select one material relevance experiment and one fusion experiment using the
   existing completed program measurements. Combine them only after their
   individual preservation arguments are clear.
5. Execute approved writer slices in connected batches. Compare original
   public/native programs, preserve ordinary limits and independent Core,
   and integrate verified retained deliveries into `codex/provider-experiments`.

The immediate deliverable is the typed pipeline/law inventory and a concrete
candidate handoff. The execution objective is reducing the compiler work that
blocks normal copying, bound-NUL copying and persistence. A selected rewrite
does not count as successful merely because it has a plausible law.

## Progress

- The isolated worktree starts from the verified original checkpoint.
- Common acknowledged shared ownership and supplied completed receipt 274,
  corrected residual attribution and the type-application fanout census.
- The [algebra study](../design/provider-experiments/analysis-algebra.md)
  records the initial source inventory, candidate laws and preservation gaps.
- Independent source review accepts F-2 as a bounded experiment with separate
  concern cuts, deferred evidence publication and charged preparation costs.
  F-1 still requires concrete typed operators and a composition proof.
- Shared Rust changes, fresh compiler measurements and rewrite acceptance
  remain pending. No Cargo window has been taken by this task.

## Verification

Review document authority, types, relative links, source anchors and evidence
provenance. Source-only law checks do not substitute for compiled evidence.
For implementations, use the plan's original end-to-end programs, connected
integration and demonstrated-bug regressions. Complete the normal integrated
repository gate before retaining a shared implementation delivery.

## Discoveries

The completed copying census attributes 1,498 of 1,534 Invoke contexts to type
applications. Four exact wrappers account for 14,936 of 16,894 Invoke-origin
slots. These are whole-analysis populations, not first-pass cost or evidence
that their environments may be merged. The equivalent NUL case has separate
source provenance.

The lexical free-value and abstract-evidence collectors traverse overlapping
bodies but have different cuts and results. Product fusion must preserve those
differences, ordering and subsequent graph-coordinate allocation.

## Deviations

Use connected batches and need-driven integration/regression tests, as directed
by the user. Keep this task-owned plan in the existing experiment package.
Do not introduce a second compiler workspace, generic profiler or semantic
change to obtain a cheaper implementation.
