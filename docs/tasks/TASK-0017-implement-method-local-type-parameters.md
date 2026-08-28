# TASK-0017: Implement Method-Local Type Parameters

- ID: `TASK-0017`
- Status: active
- Related: [CP-0010: Method-Local Type Parameters](../proposals/CP-0010-method-local-type-parameters.md), [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0009: Ordered Resolved-Global Binder Authority](../decisions/AD-0009-ordered-resolved-global-binder-authority.md), the [explicit-import evidence](../design/lib-ash/imports-evidence.md), the [explicit-kind evidence](../design/lib-ash/kinds-evidence.md), and the [execution plan](../plans/2026-08-28-method-local-type-parameters.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0010 is the accepted transition authority. The current specification owns
  implemented Ash until this product branch lands implementation, tests, and
  normative updates together.
- The branch starts from `e4fbc54`, after the integrated explicit-import and
  explicit-kind increments. Those increments supply stable identities,
  fixed-kind binders, body-free summaries, linked authentication, explicit
  implementation selection, typed Core operations, independent validation,
  and the current resource ledgers.
- Work runs on branch `feature/cp0010-method-local-type-parameters` in
  `.worktree/cp0010-method-local-type-parameters`. It remains separate from
  `main` until explicit integration approval.
- The clean baseline passes `cargo build --all-targets --all-features`,
  `cargo test --all-targets --all-features`, and `cargo xtask verify` before
  production changes.
- Every behavior change uses a witnessed red-green-refactor cycle. Production
  Rust follows `rust-skills`; unexpected failures use
  `superpowers:systematic-debugging`. Intermediate commits are unsigned.

## Work budget

The authorized work budget is 70 notional units relative to 100 units for the
preceding explicit-kind increment. Units compare checkpoint scope and risk;
they are not elapsed time, tokens, or lines changed.

| Checkpoint | Units | Cumulative |
| --- | ---: | ---: |
| Authorization and baseline | 4 | 4 |
| Syntax, resolution, and binder identity | 10 | 14 |
| Checked schemes and occurrence inference | 12 | 26 |
| Summary, import, and linked authentication | 12 | 38 |
| Core adapters, authentication, and transforms | 14 | 52 |
| Resources, migration, diagnostics, and corpus | 10 | 62 |
| Specification, evidence, reviews, and closure | 8 | 70 |

Starting any checkpoint, including a documentation checkpoint, reserves its
full allocation through corrections and review. A checkpoint may finish inside
that reserved allocation. Do not borrow from the final closure allocation. At
every checkpoint boundary, record the cumulative reserved units, commit,
witnessed RED and GREEN commands, review findings, and remaining units here.

Stop without reallocating or expanding scope when a checkpoint cannot finish
inside its reserved units, when any additional work would exceed 70, when a
required evidence category remains open at its checkpoint boundary, or when
implementation needs a semantic rule absent from CP-0010. Return to proposal
or design work before adding a persistent Core representation choice outside
AD-0007, changing a production resource limit, admitting general higher-rank
source values or dictionaries, changing selection from method-local arguments,
or changing evaluator state.

## Work

Execute the linked plan to:

- retain optional explicit fixed-kinded method binders with exact syntax,
  recovery, spans, completeness, canonical identity, order, and predecessor
  behavior for an absent list;
- retain checked method schemes separately from their monotype bodies and
  instantiate interface and method parameters while creating evidence only
  for the interface argument;
- publish selected evidence and inference-free method arguments atomically
  after complete module inference closure;
- check implementation methods under rigid head and method binders, preserve
  direct-recursive rigidity, and retain the combined parameter relationship;
- authenticate method schemes through body-free summaries, imports, routes,
  checked linking, occurrence evidence, and implementation-method facts;
- admit nested Core schemes only at authenticated generated method-evidence
  positions, lower abstract evidence by type application, and lower concrete
  or exact-current evidence through unspecialized generated adapters;
- keep canonical method identities exact while admitting one capture-free,
  order- and kind-preserving alpha-renaming for generated adapter binders;
- preserve or rebuild authentication through identity and literal-folding
  transforms, then pass fresh independent Core validation;
- retain ordinary source rank 1, reject every excluded higher-rank route, and
  preserve complete type erasure and evaluator behavior;
- inventory and exactly charge every new carrier, traversal, transform,
  failure, retry, and disposal path, including deep and wide 256 KiB-stack
  witnesses;
- retain exact library and CLI diagnostics, predecessor migration, one complete
  separately checked higher-kinded method corpus, and every required tampering
  matrix; and
- reconcile normative specification and documentation from implemented
  evidence, retain `docs/design/lib-ash/method-parameters-evidence.md`, complete
  independent reviews and the full gate, then remove transition artifacts
  without merging, pushing, tagging, or deleting the worktree.

This task excludes implicit method binders, method-local kind inference,
source `forall`, expression type application, source-visible implementation
method binders, method requirements, polymorphic recursion, general
higher-rank values, multi-parameter interfaces, determination rules,
associated outputs, defaults, specialization, dictionaries, packages,
effects, proofs, a second type or evidence pipeline, new Core interface nodes,
and evaluator semantic or state-machine changes.

## Progress

- Proposal preparation and revision reconstructed the current rank-1 method,
  summary, evidence, Core, resource, and runtime boundaries. Independent
  semantic audit found no missing rule that blocks acceptance.
- The user explicitly approved CP-0010 and authorized 70 of 100 notional work
  units without replanning. Commit `ebe4c5d` records acceptance while keeping
  the proposal prospective.
- The isolated worktree starts from `e4fbc54`. The baseline build, complete
  all-target and all-feature test suite, and `cargo xtask verify` pass before
  production changes.
- Checkpoint 1 reserves 4 units pending its lint, reviews, and authorization
  commit. No later checkpoint is reserved; 66 units remain unallocated.
- The implementation topology audit identified existing carriers and red-first
  seams. In particular, evidence selection currently fills a slot before whole
  module inference closure; CP-0010 requires pending selection followed by one
  atomic publication of the interface argument, method arguments, and choice.

## Verification

Each plan checkpoint records focused RED and GREEN commands. Completion
requires reading the complete output of:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --workspace --all-targets --all-features
cargo clippy --locked --workspace --all-targets --all-features -- -D warnings
cargo test --locked --workspace --all-targets --all-features -- --list
cargo xtask verify
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Manual and independent review covers every CP-0010 evidence requirement,
including exact binder authority, absent-list failure precedence, method-scheme
scope, inference closure, rigid implementation checking, detached summaries,
linked authentication, adapter relationships, bounded alpha-renaming, nested
scheme exclusion, transform revalidation, runtime erasure, diagnostics,
resource formulas, migration, specification authority, and lifecycle cleanup.

## Discoveries

An absent method binder list and a present explicit list require distinct
resolution states. The absent-list path must retain
`interface.method-parameter` precedence, including before an invalid kind
application; a present list must authenticate its binders and enter fixed-kind
checking.

Core authentication must precede polymorphic lowering. Admitting a nested
`Forall` before independent validation has an owning immutable relation would
make unchecked Core its own authority.

The current evidence-closure boundary selects and fills method evidence before
whole-module inference closure. The implementation must retain selection as
private pending state and fill the occurrence slot only after every method
argument is inference-free.

## Deviations

No deviation from CP-0010 is currently known. Any product evidence that exposes
missing or incorrect semantics returns to proposal or design work instead of
being decided in this task.
