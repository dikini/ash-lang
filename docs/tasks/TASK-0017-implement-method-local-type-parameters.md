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
- Checkpoint 3 reaches its implementation boundary with its reserved 12 units.
  The primary RED command `cargo test --locked --test interfaces
  polymorphic_method_occurrence_instantiates_all_binders_once -- --exact`
  exited 101 with `interface.method-parameter`: the predecessor rejected the
  nonempty list and could quantify only the interface parameter. The exact
  implementation-scheme witness failed for the same reason. The unresolved
  interface argument, unresolved method argument, and higher-order occurrence
  witnesses consequently reported `interface.method-parameter` instead of,
  respectively, `constraint.ambiguous`, `type.ambiguous`, and `type.argument`.
  The rigid-recursion and exact-current witnesses likewise stopped at the
  rejected method list. The atomic-publication RED `cargo test --locked --lib
  -- elaborate::tests::module_failure_publishes_no_earlier_occurrence_selection
  --exact` exited 101 because an earlier occurrence slot was filled before a
  later module-body failure.
- Checked method facts now retain their ordered fixed-kind binder records
  separately from the monotype. Each ordinary occurrence freshens the
  interface binder followed by all method binders, creates exactly one
  interface obligation, and privately retains the ordered method arguments.
  A same-method recursive occurrence keeps the method-local binders rigid but
  still infers its interface argument normally. Implementation checking runs
  once under rigid head then method binders and publishes that explicit scheme
  boundary. Selection closes into private staged state; complete module
  inference then zonks all occurrence arguments and atomically preflights every
  exact slot identity before any one-shot fill. Ambiguity, earlier module
  failure, and preflight failure publish no slot state.
- Resource evidence covers the new carriers and disposal routes. For
  `q = 1 + m` occurrence binders, retained resolved and Core parameter copies
  charge `2q + 1 + 2 sum(K)` type work; the two-binder exact witness is
  `2K + 7` and rejects one short. Selector method ingress charges `2m`
  binder-index records, split between retained binder records and the temporary
  duplicate index, plus canonical kind comparisons in the constraint ledger
  and `m + sum(K)` type work. For `O` staged occurrences and `M` total method
  arguments, publication precharges `M + 2O` carrier units plus exact goal
  comparisons and `M` type carriers plus zonking; exact evidence for one
  two-argument occurrence is constraint 6 and type 2, with both one-short
  failures leaving the slot empty. Publication consumes its already-owned
  slot-identity set during preflight, so it creates no second proportional
  index. Checked-interface binder cloning charges and reserves `m` records
  before publication. Pending, current-method, and filled-slot owners dispose
  every retained method-argument type iteratively on all success and failure
  paths; a 32,768-deep, 256 KiB-stack witness covers a failure after one method
  argument has already zonked.
- Final GREEN evidence is 21 architecture tests, 44 implementation tests, 20
  interface-selection tests, 33 interface tests, and 39 polymorphism tests in
  one locked invocation; 64 `interface`-filtered library tests; 114
  `elaborate`-filtered library tests; and 122 `evidence`-filtered library tests.
  `cargo fmt --check`, `cargo check --locked --all-targets`, locked workspace
  all-target/all-feature Clippy with warnings denied, and `git diff --check`
  also pass. The implementation agent used `gpt-5.6-sol` at xhigh reasoning.
  Self-review found no proposal semantic gap, persistent Core choice, resource
  limit change, selection change, evaluator change, or admitted higher-rank or
  polymorphic-recursive behavior. It corrected an over-rigid interface
  argument at recursive occurrences, made current-method scope restoration
  transactional, removed an uncharged duplicate publication index, replaced
  binder `collect` with explicit precharge and reservation, and found no new
  saturating cardinality arithmetic.
- The causally required supporting edits are limited to body-free method-binder
  kind authentication, imported fixture propagation, staged evidence auditing,
  and the extended kind-call seam in `kind.rs`, `resolve.rs`,
  `evidence_audit.rs`, and `evidence_validation.rs`. `types.rs` needs no change
  because its existing bounded type operations suffice. The specification is
  unchanged. Independent semantic and Rust/resource reviews remain pending.
  Cumulative reserved use is 26/70 and 44 units remain unreserved; Checkpoint 4
  is not reserved.
- Checkpoint 3 semantic review rejected `a9d5812`. The exact identity-equal
  prerequisite RED `cargo test --locked --test interface_selection
  identity_equal_abstract_prerequisite_dispatch_instantiates_method_locals_normally
  -- --exact --nocapture` exited 101 with `type.polymorphic-recursion`, expected
  `(_, A)`, found `(Int, Int)`. The root cause was pre-selection rigidity keyed
  only by `MethodId`, so a declared `Use<Int>` prerequisite could not exercise
  its unchanged priority over exact-current evidence. The correction freshens
  every occurrence method local before selection, retains a private conditional
  relation, and activates it only when the selected evidence root is the
  current implementation identity. Abstract prerequisites and other dispatch
  discard the condition and keep their fresh locals; method arguments remain
  outside candidate choice.
- Failure-order TDD found two further consequences of the staged relation. The
  exact RED `cargo test --locked --test polymorphism
  unrelated_method_body_failure_is_not_displaced_by_staged_recursive_dispatch
  -- --exact --nocapture` returned `type.polymorphic-recursion` instead of the
  earlier `type.definition-result`; a second exact RED showed that closing two
  staged recursive occurrences could report a different application from the
  failed body. Failed bodies now enter the extra close path only when a charged
  pending condition matches that diagnostic's application or argument span,
  and post-selection enforcement is restricted to that same site. Direct
  exact-current recursion still reuses rigid locals and reports the established
  expected/found diagnostic; unrelated body failures retain predecessor order.
- Conditional ingress for `m` method locals charges
  `2m + 2 + C(I) + sum(C(M_i))` constraint units and `|I|` type units, where
  `C` is the existing constraint Type traversal and `|I|` is the cloned
  interface-argument cell count. Atomic arguments therefore use exactly
  `4m + 4` constraint units and one type unit; the exact `m = 1` retry witness
  is 8/1 and the wide `m = 1,024` witness is 4,100/1. Selection close adds one
  precharged record per pending obligation and per conditional relation.
  Conditional enforcement charges `m` ordered traversal units plus existing
  transactional unification work. Failed-body site lookup costs zero when no
  condition exists and otherwise exactly the pending slice length. One-short
  retry tests leave pending state and slots unchanged; publication rejects
  while a selected condition remains. Both rejected and selected 32,768-deep
  conditions dismantle iteratively on 256 KiB stacks.
- Correction verification passes 21 architecture tests, 44 implementation
  tests, 23 interface-selection tests, 33 interface tests, and 40 polymorphism
  tests; 64 `interface`-filtered, 115 `elaborate`-filtered, and 128
  `evidence`-filtered library tests also pass. Formatting, all-target checking,
  strict locked workspace/all-target/all-feature Clippy, Markdown task lint,
  and diff hygiene pass. The correction agent used `gpt-5.6-sol` at xhigh
  reasoning. Self-review found no selection-precedence, Core, evaluator,
  higher-rank, polymorphic-recursion admission, resource-limit, or specification
  change. The specification remains unchanged; independent semantic and
  Rust/resource re-reviews remain pending. The Checkpoint 3 reservation remains
  12 units, cumulative reserved use remains 26/70, and 44 units remain
  unreserved.
- Checkpoint 3 semantic re-review rejected correction `8622daf` on a failed-body
  ordering case. The exact RED `cargo test --locked --test interface_selection
  unrelated_selection_failure_does_not_mask_matching_polymorphic_recursion --
  --exact --nocapture` exited 101 with `type.definition-result`, expected `A`,
  found `(A, A)`, instead of the required `type.polymorphic-recursion`. The
  failing body had staged an earlier unsatisfied `Missing<Int>` occurrence and
  a later exact-current `Repeat<Int>` recursive occurrence at the failure site.
  Full suffix closure visited the earlier obligation first, failed selection,
  and never selected or enforced the matching conditional rigidity relation;
  the failed-body path then intentionally preserved the original body error.
- Failed-body correction now performs an isolated close authenticated by the
  body evidence marker and exact application or argument span. It scans the
  pending suffix for one matching conditional occurrence, rejects duplicate
  matches, and clones, zonks, and selects only that interface argument. Only an
  exact-current selected root transfers the matching rigidity relation for
  enforcement. Earlier unrelated obligations remain pending in source order,
  method arguments remain outside candidate choice, normal successful suffix
  closure is unchanged, and no occurrence slot is published on any path.
- For pending suffix length `P` and `S` pending records after the matching
  obligation, isolated close charges
  `P + S + 2 + C_select(I)` constraint units and
  `|I| + T_zonk(I) + T_select(I)` type units. The exact two-obligation fixture
  uses 25 constraint and 3 type units; adding one trailing record makes
  `S = 1` and uses 27/3 exactly. Constraint and type one-short failures, an
  invalid marker, and duplicate matching sites preserve pending order and
  counts, selected and rigidity buffers, and every empty public slot; exact
  retry succeeds. The no-condition fast path consumes zero work. Focused
  evidence also proves that an earlier unrelated selection failure is not
  visited and that a remaining pending obligation prevents publication.
- Second-correction verification passes 21 architecture tests, 44
  implementation tests, 24 interface-selection tests, 33 interface tests, and
  40 polymorphism tests; 64 `interface`-filtered, 115 `elaborate`-filtered, and
  130 `evidence`-filtered library tests also pass. Formatting, locked all-target
  checking, strict locked workspace/all-target/all-feature Clippy, Markdown
  task lint, diff hygiene, and intended-path status inspection pass. The
  correction agent used `gpt-5.6-sol` at xhigh reasoning. Self-review found no
  selection-precedence, Core, evaluator, higher-rank, polymorphic-recursion
  admission, resource-limit, or specification change. The specification is
  unchanged; independent semantic and Rust/resource re-reviews remain pending.
  The Checkpoint 3 reservation remains 12 units, cumulative reserved use
  remains 26/70, and 44 units remain unreserved.
- Checkpoint 3 quality/resource review rejected `698b99a` with three important
  findings. The nested-call RED `cargo test --locked --test
  interface_selection nested_same_method_calls_prefer_the_whole_failed_application
  -- --exact --nocapture` exited 101 because the pipeline returned an internal
  failure: the inner whole-application span equaled the outer argument span,
  and unranked raw-span uniqueness treated both valid occurrences as duplicate
  matches. The normal-close reservation RED showed zero selected-output
  capacity after the first pending record had already moved. Method-scheme
  ingress RED measured 19 constraint units instead of the required 20 for one
  binder, while the 1,024-binder one-short boundary incorrectly succeeded.
- Failed-body correlation now ranks one unique whole-application match before
  one unique argument-span fallback, then one occurrence-only match. Duplicate
  matches reject only within the selected rank, so a unique higher-rank match
  supersedes lower-rank collisions. The nested source fixture now reports
  `type.polymorphic-recursion`, expected `A`, found `Bool`, and never promotes
  valid source geometry to an internal failure. The scan remains one charged
  pass over the pending suffix, allocates no index, and does not inspect method
  arguments or change candidate choice.
- Normal close uses its existing `P + R` precharge for `P` selected occurrence
  outputs and `R` conditional rigidity outputs, then reserves both complete
  buffers before reversing or draining pending records. No fallible allocation
  of selected-output vector capacity remains after mutation; exact evidence
  preserves source order and rigidity indices 0 and 2 around an ordinary middle
  occurrence.
  Method-scheme ingress now atomically charges `2m` constraint records before
  reserving the retained binder sequence and temporary duplicate index. Its
  method-specific constraint formula is `C(V) + 2m + sum(1 + C(K_i))`, where
  `C(V)` is the existing type traversal and `C(K_i)` is fixed-kind comparison.
  The wide kind-`Type`
  fixture, including interface ingress, is exactly `7m + 11` constraint and
  `3m + 5` type units: at `m = 1,024`, 7,179/3,077. One-short failure publishes
  no interface or method index, and exact retry succeeds.
- Third-correction verification passes 21 architecture tests, 44
  implementation tests, 25 interface-selection tests, 33 interface tests, and
  40 polymorphism tests; 64 `interface`-filtered, 115 `elaborate`-filtered, and
  133 `evidence`-filtered library tests also pass. Formatting, locked all-target
  checking, strict locked workspace/all-target/all-feature Clippy, Markdown
  task lint, diff hygiene, and intended-path status inspection pass. The
  correction agent used `gpt-5.6-sol` at xhigh reasoning. Self-review found no
  selection-precedence, Core, evaluator, higher-rank, polymorphic-recursion
  admission, resource-limit, or specification change. The specification is
  unchanged; independent semantic and Rust/resource re-reviews remain pending.
  The Checkpoint 3 reservation remains 12 units, cumulative reserved use
  remains 26/70, and 44 units remain unreserved.

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
