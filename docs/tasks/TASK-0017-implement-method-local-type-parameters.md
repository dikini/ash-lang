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
- Checkpoint 1 completes at `9f90176` and consumes its reserved 4 units. No
  production RED applies to this documentation-only checkpoint; the authority
  RED was an accepted proposal with no active task or plan. GREEN evidence is
  `cargo build --all-targets --all-features`,
  `cargo test --all-targets --all-features`, `cargo xtask verify`, focused
  Markdown lint, relative-link resolution, and diff hygiene. The repeated
  semantic/authority and artifact/plan-quality reviews approve with no open
  finding. No later checkpoint is reserved; 66 units remain.
- The implementation topology audit identified existing carriers and red-first
  seams. In particular, evidence selection currently fills a slot before whole
  module inference closure; CP-0010 requires pending selection followed by one
  atomic publication of the interface argument, method arguments, and choice.
- Checkpoint 2 completes with its reserved 10 units. The syntax RED command
  `cargo test --locked --test interfaces_syntax
  projects_method_local_type_parameters_and_kinds -- --exact` first failed
  because `SurfaceInterfaceMethod` had no binder list, then failed because the
  parser reported a missing `:` at `<`. The malformed-list exact test likewise
  reported a missing `:` instead of the causal list failure. The resolution RED
  command `cargo test --locked --test resolution
  method_type_binders_are_complete_ordered_and_declaration_ordered -- --exact`
  returned occurrence order `A, B, G`, all at kind `Type`, instead of written
  order `B, A, G : Type -> Type`. The focused kind RED accepted a method that
  used `F : Type -> Type` in a value-type position because predecessor kinding
  deferred every nonempty method parameter set.
- GREEN evidence is `cargo test --locked --test interfaces_syntax` with 28
  tests, `cargo test --locked --test resolution` with 52 tests,
  `cargo test --locked --test kinds` with 22 tests, `cargo test --locked --test
  diagnostics` with 34 tests, `cargo fmt --check`, `cargo check --locked
  --all-targets`, and `git diff --check`. Self-review checked CP-0010 scope,
  absent-list precedence, signature-only scope, canonical declaration order,
  fixed kinds, parser recovery ownership, Rust ownership and error paths, and
  diff scope. It corrected the method-colon recovery label and the required
  all-target test-fixture initializers and found no remaining actionable issue.
  The first semantic review approved this implementation; the first
  Rust/resource review produced the correction findings recorded below.
- The independent Rust/resource review of Checkpoint 2 reported two important
  findings and one minor finding. First, repeated interface-parameter
  installation charged an unchanged absent-list method once per method.
  `kind::tests::absent_method_lists_preserve_predecessor_owner_install_accounting`
  failed at the predecessor formula of one owner installation plus each
  method's unchanged work. Second, present method-list validation allocated and
  traversed proportional duplicate indexes without type-work accounting or
  fallible reservation. The exact validation test showed that a one-short
  two-binder fixture succeeded. Third, the resolved boolean discriminator
  admitted the impossible state `explicit + empty` through kind checking.
- The corrections retain one interface-only environment across consecutive
  absent-list methods, reset it for every explicit method and after explicit
  locals, and reject `explicit + empty` at resolved kind admission. A present
  list with `P` binders now charges `1 + P` validation units atomically before
  fallible declaration and duplicate-index reservation. Exact duplicate-owner
  and duplicate-local failures retain their spans; one-short failure leaves no
  method binder identity published and an exact fresh retry succeeds. The new
  exact unit tests and the four focused integration suites pass, as do
  formatting, all-target checking, Clippy with warnings denied, and diff
  hygiene. Self-review found no remaining correction issue.
- Independent semantic re-review at `86e32dd` approves the combined Checkpoint
  2 diff with no finding. Independent Rust/resource re-review confirms all
  three original findings are closed and reports no new finding. The
  implementation and correction agents used `gpt-5.6-sol` at high reasoning;
  semantic review used `gpt-5.6-sol` at xhigh reasoning, and Rust/resource
  review used `gpt-5.6-sol` at high reasoning.
- Root verification after both reviews passes 646 library tests and all 136
  tests in `interfaces_syntax`, `resolution`, `kinds`, and `diagnostics`, plus
  `cargo fmt --check`, locked all-target checking, locked workspace all-target
  and all-feature Clippy with warnings denied, and diff hygiene. The initial
  diff-hygiene invocation named an incorrect expanded base hash after every
  preceding command had passed; resolving `d415111` to its repository identity
  and rerunning the failed hygiene tail passed without a code change.
- Checkpoint 2 is complete in `faeb689` plus correction `86e32dd`. Its reserved
  10 units do not change during correction and review: cumulative reserved use
  is 14/70, 56 units remain, and Checkpoint 3 is not reserved.

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
