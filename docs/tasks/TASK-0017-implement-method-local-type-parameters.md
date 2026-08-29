# TASK-0017: Implement Method-Local Type Parameters

- ID: `TASK-0017`
- Status: active
- Related:
  [CP-0010: Method-Local Type Parameters][cp-0010],
  [DN-0025: Library and Package Milestones][dn-0025],
  [AD-0006: Front-End Semantic Boundaries][ad-0006],
  [AD-0007: Typed Core Dialects][ad-0007],
  [AD-0009: Ordered Resolved-Global Binder Authority][ad-0009],
  the [explicit-import evidence][import-evidence],
  the [explicit-kind evidence][kind-evidence], and
  the [execution plan][execution-plan]

[cp-0010]: ../proposals/CP-0010-method-local-type-parameters.md
[dn-0025]: ../design/DN-0025-library-and-package-milestones.md
[ad-0006]: ../decisions/AD-0006-front-end-semantic-boundaries.md
[ad-0007]: ../decisions/AD-0007-typed-core-dialects.md
[ad-0009]: ../decisions/AD-0009-ordered-resolved-global-binder-authority.md
[import-evidence]: ../design/lib-ash/imports-evidence.md
[kind-evidence]: ../design/lib-ash/kinds-evidence.md
[execution-plan]: ../plans/2026-08-28-method-local-type-parameters.md

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
- Independent semantic re-review approves `994ab9f` with no critical,
  important, or minor findings. It independently exercised identity-equal and
  generic prerequisites, exact-current recursion, an earlier unrelated
  unsatisfied obligation, nested equal-boundary applications, ambiguity,
  publication, and higher-order rejection. Ranked failure correlation retains
  abstract-prerequisite priority and reports the nested exact-current witness
  as `type.polymorphic-recursion`, expected `A`, found `Bool`; no temporary
  review fixture remains.
- Independent Rust/resource re-review also approves `994ab9f` with no critical,
  important, or minor findings. It verified the complete `P + R` normal-close
  preallocation boundary, ranked same-tier duplicate rejection, exact selected
  order and rigidity indices, checked `2m` method-scheme ingress, one-short
  atomic retry, private publication state, iterative disposal, and the absence
  of dependency, production-limit, specification, Core, evaluator, Checkpoint
  4, or Checkpoint 5 changes. Its fresh focused counts are 21 architecture, 44
  implementation, 25 interface-selection, 33 interface, and 40 polymorphism
  tests plus 64 `interface`-, 115 `elaborate`-, and 133 `evidence`-filtered
  library tests.
- Fresh root verification at the reviewed head passes all 663 library tests and
  the five focused integration suites with counts 21/44/25/33/40. Formatting,
  locked all-target checking, strict locked workspace/all-target/all-feature
  Clippy, task Markdown lint, combined-diff hygiene, and clean-worktree status
  also pass. Checkpoint 3 is complete in `a9d5812`, `8622daf`, `698b99a`, and
  `994ab9f`. Its reserved use is 12 units, cumulative reserved use is 26/70,
  44 units remain unreserved, and Checkpoint 4 is not reserved.
- Checkpoint 4 starts from the clean reviewed boundary `23f35bd` and reserves
  its planned 12 units for summary, import, route, and linked-evidence
  authentication. Cumulative reserved use is 38/70, 32 units remain
  unreserved, and Checkpoint 5 is not reserved. This reservation does not
  authorize Core lowering, adapters, transformations, runtime changes, or
  specification reconciliation from later checkpoints.
- Checkpoint 4 reaches its implementation review boundary. The detached
  summary RED was
  `cargo test --locked --test interface_generic_summary
  detached_summary_preserves_complete_method_scheme -- --exact`: the consumer
  failed kind checking because the imported method binders had been discarded.
  The summary-tampering RED admitted an independently forged binder origin,
  and the linked RED rejected every nonempty occurrence method-argument list
  because the combined registry omitted method binders. The corresponding
  GREEN witnesses cover the complete summary mutation matrix, exact private
  binder authority, linked occurrence argument/type/identity tampering,
  implementation head-then-method ordering, and the linked generic facade
  diamond.
- The new exact resource boundaries charge one graph fact per private
  polymorphic-method authority row and `1 + K` type units per retained binder
  record with a `K`-node kind. The two-`Type`-kind fixture therefore succeeds
  at constraint/type limits `1/4` and fails atomically one short on either
  ledger. Evidence publication charges `2 + 1 + 2 + 2 = 7` constraint units
  for two method arguments, one checked-value carrier, two occurrence/slot
  records, and the selected-goal comparison, plus two type units. Conditional
  rigidity ingress charges the preceding eight units plus one checked-value
  carrier and its two-cell walk, for `11/1` constraint/type units. All use
  checked arithmetic, fallible pre-reservation, exact retry, and iterative
  disposal.
- One imported generic method with a five-cell monotype uses `1 + 3 + 2(5) +
  3 = 17` constraint units for its route, retained facts, type traversals, and
  binder authentication; its corresponding type retention uses `3 + 2(5) +
  2(1 + 1) = 17` units. Adding one `Type`-kind method binder to the combined
  registry adds four constraint units for uniqueness, the binder visit,
  Source-Origin, and Type-Kind authentication, plus three type units for its
  record, Kind, and canonical staging cell. Both boundaries reject one-short
  attempts without publication and accept an exact retry.
- Focused GREEN verification passes 40 evidence-selection, 80 summary and
  combined-registry, 43 resolver, and 81 linked-validation library tests. The
  planned integration bundle passes 21 architecture, 2 generic-summary, 1
  linked identity-diamond, 20 interface-module, 14 library-import, 2
  interface-validation, and 8 module-elaboration tests. The implementation
  agent used `gpt-5.6-sol` at xhigh reasoning. Complete-diff self-review found
  and corrected checked-value late-failure disposal and the driver's exact
  one-unit capability prefix. The locked all-target/all-feature workspace
  test passes 668 library tests and every integration and binary suite;
  formatting, checking, strict Clippy, test listing, `cargo xtask verify`, task
  Markdown lint, and diff hygiene pass. Independent semantic and Rust/resource
  reviews remain pending. The Checkpoint 4 reservation remains 12 units,
  cumulative reserved use is 38/70, 32 units remain unreserved, and Checkpoint
  5 is not reserved.
- Checkpoint 4 semantic review rejected `652f74c` with two important findings
  and no critical or minor findings. The exact pre-publication authority RED,
  `cargo test --locked --lib
  resolved::tests::freeze_rejects_coherently_forged_checked_method_binder_before_publication
  -- --exact`, failed because a resolved `A` binder and a coherently forged
  checked `Forged` binder, identity, origin, and body scope were accepted. The
  exact linked-identity RED, `cargo test --locked --lib
  evidence_validation::tests::rejects_same_shaped_method_occurrence_identity_substitution
  -- --exact`, failed because changing only `first<A>` to the same-shaped
  `second<B>` occurrence still validated.
- Checked interface facts now own a private defining-source authority row for
  every method, including monomorphic methods. Each row retains its stable
  `MethodId` and complete ordered binder records. Checking mints the rows from
  resolved source; imports, public and hidden summary mirrors, facades, and
  diamond routes clone already-authenticated rows. Freeze authenticates exact
  method order, identity, spelling, span, origin, monotype, binder identity,
  binder spelling, binder origin, kind, owner, and body scope before
  publication. Detached authentication and alternate-route equality consume
  the private rows rather than minting authority from a checked mirror. Missing
  monomorphic rows reject, the combined registry still counts each logical
  binder once, and a 32,768-deep private binder origin disposes on a 64 KiB
  stack.
- Method obligations now retain the originally checked `MethodId` through
  pending selection, selected occurrences, the private publication map, and
  `FilledEvidenceSlot`. Publication atomically moves that identity with the
  interface argument, method arguments, checked value type, and selection;
  ordinary global slots retain `None`. Linked validation first requires exact
  equality with the occurrence identity, then authenticates an abstract root's
  `MethodId` or a concrete and exact-current root's
  `ImplMethodId::new(selected_impl, method)`. It does not reselect evidence and
  method arguments do not affect candidate choice. Dedicated tampering
  witnesses reject the retained identity alone, occurrence identity alone,
  wrong abstract relationship, wrong concrete relationship, and wrong
  exact-current relationship; the checked-body audit also rejects a staged
  identity that differs from the occurrence.
- Corrected resource witnesses charge one constraint unit per retained or
  authenticated private method row and retain each copied binder record and
  kind on TypeWork without adding a second logical registry variable. Two
  `Type` binders clone at exact constraint/type limits `1/4`; the generic hidden
  import boundary is `18/19`. One method occurrence with one method argument,
  one rigidity argument, and a checked `Unit` value enters at `12/1`; width
  `W` enters at `(4W + 8)/1`. Two method arguments publish at `8/2`, including
  the retained method identity. A private one-method interface checks at 48
  constraint units, while the implementation fixture checks at 93. For the
  public wide graph, dependency checking is `48W`, entry resolution is
  `65W + 1`, entry checking is `75W + 12`, linking is `78W + 24`, and linked
  validation is `123W + 69`. At test width 4,000, linking remains below the
  unchanged 327,680-unit production limit and validation crosses it. All
  exact boundaries reject one-short attempts without publication and accept a
  clean retry; no production limit changed.
- The predecessor width-5,000 resource fixtures were already intentionally
  invalid: one exhausted the shared default budget during linked validation,
  and one contained a prerequisite cycle whose diagnostic had to precede
  unrelated resource exhaustion. Required Checkpoint 4 authority work moves
  the width-5,000 cumulative prefix to 240,000 after dependency checking,
  325,001 after entry resolution, and 375,012 during entry checking, so that
  padding now exhausts before either intended owner. Recalibrating only those
  stress fixtures to width 4,000 yields 192,000, 260,001, 300,012, and 312,024
  through linking, then 492,069 after validation. The unchanged default limit
  therefore preserves the original validation-exhaustion and cycle-precedence
  contracts. No previously successful program becomes a regression witness;
  the old sources were deliberate rejection cases.
- Correction verification passes all 677 library tests, the planned 68-test
  Checkpoint 4 bundle with counts 21/2/1/20/14/2/8, and all three cross-stage
  resource tests. The locked workspace/all-target/all-feature command passes
  1,477 tests across 47 suites with no failures or ignored tests. Formatting,
  locked all-target checking, strict locked workspace/all-target/all-feature
  Clippy, test listing, `cargo xtask verify`, Markdown lint, and diff hygiene
  pass. The correction agent used `gpt-5.6-sol` at xhigh reasoning.
  Self-review corrected an uncharged
  quadratic authority lookup to ordered linear consumption, added the required
  row for monomorphic methods, moved cheap top-level alternate-route identity
  rejection before private-row traversal to preserve precedence, strengthened
  source method origin and monotype authentication, made the construction API
  accept the resolved interface directly, added deep private-row disposal, and
  recalibrated only already-invalid wide resource fixtures to preserve their
  owning phase and diagnostic precedence. The Checkpoint 4 reservation remains
  12 units, cumulative reserved use remains 38/70, 32 units remain unreserved,
  independent semantic and Rust/resource re-reviews remain pending, and
  Checkpoint 5 is not reserved.
- Checkpoint 4 quality review rejected correction `2bf317a` with one important
  and one minor finding. The accepted-capacity RED,
  `cargo test --locked --test interface_resources
  monomorphic_interface_capacity_preserves_predecessor_default_acceptance
  -- --exact`, failed at linked evidence validation under the unchanged
  327,680-unit production limit: 2,800 public monomorphic interfaces reached
  344,469 cumulative constraint units because the private authority vector
  allocated and traversed one scalar row per method. The focused unused-buffer
  RED, `cargo test --locked --lib
  evidence_validation::tests::generic_implementation_validation_excludes_discarded_head_scope_buffer_work
  -- --exact`, measured seven units instead of six because implementation-body
  validation charged, allocated, and filled a head-parameter vector that no
  consumer read.
- The second correction attaches a module-private
  `Option<Box<[ResolvedTypeVariable]>>` directly to each existing checked
  method fact. `None` is exact for a monomorphic method and owns no allocation,
  scalar graph fact, or authority traversal. `Some` is exact for a polymorphic
  method and owns an independently cloned, source-derived binder payload.
  Local checking can mint it only through a resolved-source constructor;
  import and summary retention can clone it only through a constructor whose
  source is an already-authenticated checked method. Public and hidden summary
  facts, facade and diamond routes, checker views, the combined registry,
  selection ingress, linked consistency, implementation relations, and
  occurrence validation consume the private slice. Missing polymorphic
  payloads and surplus empty payloads reject, while deep payload teardown stays
  iterative.
- The source-to-summary invariant remains complete without reinstating
  per-monomorphic authority work. Freeze checks every method's defining
  identity, spelling, declaration order, owner, and span. For a polymorphic
  method it additionally checks resolved-source origin and monotype, exact
  source-to-private binders, and exact private-to-checked binders before
  publication. Detached summary authentication checks the private/public
  binder biconditional, identity, order, spelling, origin, kind, canonical
  owner, and value-type body scope; its interface owner and declaration-
  ordinal checks make method alignment structural. At the linked boundary,
  `validate_group_consistency` independently checks method identity, spelling,
  span, origin, monotype, source-to-private binders, and private-to-checked
  binders. The existing
  `rejects_every_task8_kinded_linked_diamond_carrier_before_core` matrix covers
  source method identity, spelling, span, local binder, checked method origin,
  and checked method type mutations; the summary carrier and hidden-diamond
  matrices cover public/hidden method type, free-binder, kind, identity, owner,
  origin, and span mutations. The coherent pre-freeze forge and complete
  detached binder-tampering matrix remain GREEN.
- Monomorphic accounting returns exactly to the predecessor boundary:
  dependency checking is `37W`, entry resolution is `52W + 1`, entry checking
  is `62W + 12`, linking is `65W + 24`, and linked validation is `110W + 69`.
  The sole scalar `+1` is the already-recorded successful validation
  capability, not per-method authority work. The default 2,800-interface
  witness therefore succeeds at 308,069, leaving 19,611 units, and both
  predecessor width-5,000 rejection fixtures again reach their intended
  validation-exhaustion and cycle owners. A polymorphic payload still clones
  at exact constraint/type limits `1/4`, and the generic hidden-import boundary
  remains `18/19`. Removing the obsolete implementation-head buffer saves
  exactly head width `H` constraint units, one allocation, and `H` writes with
  no TypeWork change; the one-head, one-method witness rejects at five and
  succeeds reproducibly at six.
- Second-correction focused GREEN evidence passes 679 library tests, the
  planned 47 product tests with counts 2/20/1/14/2/8, all 21 architecture
  tests, and all four cross-stage resource tests. The correction agent and
  independent capacity audit used `gpt-5.6-sol` at xhigh reasoning. Complete
  workspace verification passes all 1,480 tests, strict Clippy with warnings
  denied, formatting, metadata, documentation generation, Markdown lint, and
  diff hygiene. Self-review additionally changed imported implementation-body
  checking to consume the private authoritative binder slice directly; the
  local path continues to consume resolved source authority. Independent
  semantic and Rust/resource re-reviews remain pending. The Checkpoint 4
  reservation remains 12 units, cumulative reserved use remains 38/70, 32
  units remain unreserved, and Checkpoint 5 is not reserved.
- Checkpoint 4 semantic re-review rejected correction `f027da9` with one
  important finding. The exact RED,
  `cargo test --locked --lib
  resolved::tests::freeze_rejects_coherently_forged_monomorphic_method_type_and_origin_before_publication
  -- --exact`, kept the canonical method identity, spelling, owner, order,
  span, empty binder mirror, and `None` private payload while replacing the
  source monotype and origin; `ExportSummary::freeze` incorrectly returned a
  publishable summary. The source-authentication branch had guarded origin and
  monotype comparison on a nonempty method-binder payload.
- The third correction authenticates source origin and monotype for both
  monomorphic and polymorphic local methods while cloning the body-free
  summary fact. The already-reserved method relation authenticates the first
  origin node, with each deeper origin node charged separately. A fallible
  paired type worklist authenticates exact source/checked equality during the
  existing charged summary-clone traversal, so successful work equals the
  preceding `charge_type` boundary rather than adding a second traversal.
  Binder presence and private/public/source equality retain their previous
  order and ownership. Imported mirrors still clone only already-authenticated
  private authority, and local dependent checking consumes that private slice.
  No monomorphic row, allocation, registry entry, or production-limit change
  was introduced.
- The new source-origin/type RED is GREEN for the combined forge and for each
  mutation independently. The paired traversal rejects one-short, succeeds
  exactly and reproducibly at six cells for a three-node function, and remains
  exact and stack-safe at `4D + 2` for depth `D = 32,768`. The existing
  polymorphic coherent forge, complete detached binder matrix, linked-diamond
  carrier matrix, deep and wide summary tests, all four cross-stage resource
  tests, and the default 2,800-interface acceptance witness remain GREEN.
  Monomorphic cumulative accounting remains `37W`, `52W + 1`, `62W + 12`,
  `65W + 24`, and `110W + 69`; the default witness still ends at 308,069.
  Focused verification passes all 682 library tests, the planned 47 product
  tests with counts 2/20/1/14/2/8, all 21 architecture tests, and all four
  cross-stage resource tests. Complete workspace verification passes all
  1,483 tests, strict Clippy with warnings denied, formatting, compilation,
  metadata, documentation generation, Markdown lint, and diff hygiene. The
  correction used `gpt-5.6-sol` at xhigh reasoning. Independent semantic and
  Rust/resource re-reviews remain pending. The Checkpoint 4 reservation
  remains 12 units, cumulative reserved use remains 38/70, 32 units remain
  unreserved, and Checkpoint 5 is not reserved.
- Checkpoint 4 semantic re-review rejected correction `a96e49a` with one
  important finding and no other findings. The exact RED,
  `cargo test --locked --lib
  evidence_validation::tests::rejects_forged_implementation_head_method_partition_before_capability
  -- --exact`, changed only an implementation method's stored
  `head_type_parameter_count` from one to zero while preserving its canonical
  four-binder head-then-method scheme. Linked validation incorrectly returned
  a `ValidatedInterfaceProgram` and its method-evidence capability because it
  compared only the concatenated binder sequence.
- The fourth correction requires the stored partition to equal the canonical
  implementation head length at the linked per-method boundary before the
  existing concatenated-binder authentication. The scalar comparison executes
  in the already-charged method-relation slot and adds no allocation, carrier,
  row, constraint unit, TypeWork unit, or production-limit change. The exact
  partition RED is GREEN and publishes no capability. The positive
  polymorphic implementation, reordered head-then-method binder, source
  authority, method identity, deep, one-short, and accepted-capacity witnesses
  remain GREEN.
- Resource accounting remains `37W`, `52W + 1`, `62W + 12`, `65W + 24`, and
  `110W + 69`; the default 2,800-interface witness still succeeds at 308,069.
  The generic implementation-body boundary remains six units. Focused
  verification passes all 683 library tests, the planned 47 product tests with
  counts 2/20/1/14/2/8, all 21 architecture tests, and all four cross-stage
  resource tests. Complete workspace verification passes all 1,484 tests. The
  correction used `gpt-5.6-sol` at xhigh reasoning. Formatting, locked
  all-target compilation, strict locked workspace/all-target/all-feature
  Clippy, test listing, `cargo xtask verify`, documentation generation,
  Markdown lint, and diff hygiene pass. Independent semantic and Rust/resource
  re-reviews remain pending. The Checkpoint 4 reservation remains 12 units,
  cumulative reserved use remains 38/70, 32 units remain unreserved, and
  Checkpoint 5 is not reserved.
- Checkpoint 4 quality/resource re-review rejected correction `35dce7d` with
  two important findings and one minor finding. Seven authority-discovery
  loops traversed every method while charging only nonempty binder slices;
  charging those hidden visits would have raised the 2,800-interface witness
  to `117W + 69 = 327,669`, leaving only 11 units below the production limit.
  Linked occurrence authentication also searched every selected method row,
  making final-method occurrences linear in interface width. Finally, the
  `Forall` branch of exact type comparison delegated Kind equality to an
  infallibly allocated and grown paired worklist.
- The fifth correction removes the method-derived combined-registry count,
  owner-authentication, and retention prepasses. Combination counts and clones
  the canonical registry map once; nominal and global ordered mirrors remain
  independent. Exact method-owner/cardinality authentication moves to the
  linked boundary's already-charged canonical method-index pass, before any
  validation capability or Core can publish. A surplus canonical variable is
  now rejected at that boundary. Imported interface retention charges binder
  work in its existing canonical method pass and records only the ordinals of
  polymorphic authority-bearing methods. The checker view follows that private
  index, so monomorphic interfaces retain an empty allocation-free index and
  perform no separate method discovery. The wide phase witness asserts both
  the empty index and unchanged cumulative boundaries. One polymorphic hidden
  import now owns the additional discovery-index graph slot at exact
  constraint/type limits `19/19`; monomorphic accounting has no delta.
- Occurrence authentication now converts the retained `MethodId` declaration
  ordinal and performs one bounds-checked indexed read. The abstract relation
  requires the exact `MethodId`; concrete and exact-current relations require
  `ImplMethodId::new(selected_impl, checked_method)`. A 32,768-wide final-slot
  witness observes one identity comparison for success and wrong-slot
  rejection, zero for an out-of-range ordinal, and no fallback search. The
  host comparison bound is at most one per method occurrence, with zero
  allocation, ConstraintWork, TypeWork, candidate selection, or formula delta.
- `InterfaceConstraintBudget` now owns a fallible iterative paired-Kind
  worklist for exact `Forall` comparison. The root and each child are charged
  before `try_reserve` and push. Successful work remains one unit per Kind node
  and exactly matches `charge_type`: a three-element tuple uses 12 units, one
  binder with a five-node nested-arrow Kind uses 10, and depth `D = 32,768`
  uses `2D + 6` on a 64 KiB stack. Tuple, `Forall`, and nested-arrow Kind
  success, mismatch, one-short rejection, and clean retry are covered. The new
  borrowed paired-Kind worklist is recorded in the closed architecture
  inventory.
- The original hidden-loop review witness is GREEN without charging the seven
  monomorphic scans: cumulative work remains `37W`, `52W + 1`, `62W + 12`,
  `65W + 24`, and `110W + 69`. The default `W = 2,800` program succeeds at
  308,069 and retains 19,611 units of headroom under the unchanged 327,680
  limit. Focused verification passes 687 library tests, the planned 47 product
  tests with counts 2/20/1/14/2/8, all 21 architecture tests, and all four
  cross-stage resource tests. Complete locked workspace verification passes
  all 1,488 listed tests. Formatting, locked all-target compilation, strict
  locked workspace/all-target/all-feature Clippy, test listing, `cargo xtask
  verify`, documentation generation, Markdown lint, and diff hygiene pass. The
  correction agent used `gpt-5.6-sol` at xhigh reasoning; read-only
  authority-loop and method-lookup audits used xhigh and high reasoning. The
  Checkpoint 4 reservation remains 12 units, cumulative reserved use remains
  38/70, 32 units remain unreserved, independent semantic and Rust/resource
  re-reviews remain pending, and Checkpoint 5 is not reserved.
- Independent semantic re-review approves `9e5aa3a` with no critical,
  important, or minor findings. It verified that canonical registry retention
  no longer derives authority through method-mirror scans; linked method-owner
  insertion, duplicate and surplus rejection, and final cardinality execute in
  the charged canonical method-index pass before capability publication. It
  also rechecked source/private/checked binder equality, body scope,
  provenance, monotype, implementation partition, import ordinals, exact
  `MethodId` and `ImplMethodId` relationships, fallible paired type and Kind
  equality, atomic publication, and the absence of Core, evaluator,
  specification, selection-policy, or Checkpoint 5 changes. Its fresh evidence
  passes 91 evidence-validation-filtered and 102 resolved-filtered library
  tests, the 68-test planned-plus-architecture bundle, all four resource tests,
  formatting, focused and aggregate diff hygiene, and clean status.
- Independent Rust/resource re-review also approves `9e5aa3a` with no critical,
  important, or minor findings. It confirmed that all seven hidden
  monomorphic method scans are removed or fused into charged canonical passes,
  empty monomorphic authority indexes allocate no backing storage, and the
  exact cumulative formula remains `110W + 69` because no proportional host
  work is omitted. It verified one bounds-checked ordinal lookup and one exact
  comparison per in-range method occurrence, with no fallback search, and
  charge-before-reserve fallibility plus successful work parity for every Type
  and Kind shape. Its fresh focused, resource, combined-registry,
  linked-registry, deep-drop, and architecture tests pass, as do all 1,488
  listed workspace tests, formatting, locked all-target checking, strict
  Clippy, `cargo xtask verify`, documentation generation, Markdown lint,
  aggregate diff hygiene, and clean status.
- Fresh root verification at the reviewed head passes all 687 library tests,
  all 21 architecture tests, the planned 47 product tests with counts
  2/20/1/14/2/8, and all four cross-stage resource tests. The complete locked
  workspace/all-target/all-feature run and `cargo xtask verify` pass all 1,488
  listed tests. Formatting, locked workspace/all-target/all-feature checking,
  strict Clippy with warnings denied, rustdoc, Markdown lint, aggregate diff
  hygiene, exact head inspection, and clean-worktree status also pass.
  Checkpoint 4 is complete in `652f74c`, `2bf317a`, `f027da9`, `a96e49a`,
  `35dce7d`, and `9e5aa3a`. Its reserved use is 12 units, cumulative reserved
  use is 38/70, 32 units remain unreserved, and Checkpoint 5 is not reserved.
- Checkpoint 5 starts from the clean reviewed boundary `61e3d77` and reserves
  its planned 14 units for authenticated polymorphic Core evidence, generated
  adapters, independent validation, and transform preservation. Cumulative
  reserved use is 52/70, 18 units remain unreserved, and Checkpoint 6 is not
  reserved. This reservation does not authorize new Core interface nodes,
  dictionaries, body specialization or copying, evaluator state or behavior,
  general nested schemes, selection changes, specification reconciliation, or
  a persistent representation choice outside AD-0007.
- Checkpoint 5's two lowering REDs are witnessed before production changes.
  `cargo test --locked --test core_validation
  abstract_polymorphic_method_evidence_instantiates_at_retained_arguments --
  --exact --nocapture` exited 101 while elaborating the abstract occurrence:
  the retained `(Int, Bool)` method arguments were not type-applied, so the
  monomorphic evidence function still required `(I, A, B)`. `cargo test
  --locked --test core_validation
  concrete_method_evidence_uses_one_generated_adapter -- --exact --nocapture`
  exited 101 with `Internal(InvalidState)`: concrete lowering exposed the
  implementation method directly and could not construct the required
  expression-local polymorphic adapter. Both failures are at the intended
  predecessor seams; no evaluator, specification, resource limit, selection,
  or production source changed for the REDs.
- Checkpoint 5's abstract and concrete verticals are GREEN. Abstract evidence
  retains the authenticated method arguments in an exact `TypeApplication`;
  concrete evidence builds one capture-free method-local adapter over the
  selected implementation and its ordered prerequisite applications. Focused
  Core validation also passes two polymorphic domain positions in declaration
  order, direct exact forwarding without adapter or reselection, and
  exact-current recursion with an active abstract prerequisite. The ordinary
  monomorphic path and the evaluator remain unchanged.
- The linked CP5 authority is one immutable private catalog plus exact Core
  anchors. It retains canonical methods, every relevant implementation owner,
  exact definition domains and occurrences, adapters and prerequisite edges,
  and stable expectation indexes. Builder publication consumes each expected
  event once; independent validation repeats consumption and checks owner
  envelopes, complete application and forwarding relations, selected
  implementation identity, source instantiation, ordered prerequisites,
  bounded complete alpha-renaming, and exclusive incoming uses. Private
  mutation matrices reject missing, extra, duplicate, stale, wrong-index,
  owner, requirement, position, method, interface, scheme, producer,
  instantiation, adapter, forwarding, alpha capture, shadow, escape, storage,
  return, and owner-envelope tampering. Unauthenticated nested schemes remain
  rejected through binding, storage, and return routes.
- Identity and literal-fold transforms remap every authority anchor, preserve
  the catalog by `Arc` identity, and freshly revalidate; representative
  post-transform tampering is rejected. Exact resource probes pass at 87
  constraint and 74 type units for linked catalog construction, 14 units for
  one Builder anchor and finish, 2,219 units for independent validation, six
  type units for one scope-entry row, and 307/303 units for identity/fold
  transform replay. Every retained scalar, reference, Type, Kind, selection
  edge, worklist, map, and carrier capacity is charged before reserve or
  publication. One-short rejection and fresh exact retry are covered at each
  seam. Deep accepted/rejected scoped arguments and linked authority teardown
  pass on 256 KiB stacks; shared catalog `Weak` handles reach zero and no cycle
  remains.
- CP5 implementation verification currently passes 702 library tests, all 61
  Core-validation integration tests, all 21 architecture tests, and the
  complete 1,508-test locked workspace/all-target/all-feature matrix. Locked
  checking, strict Clippy with warnings denied, test listing, `cargo xtask
  verify` including rustdoc, Markdown lint, and diff hygiene also pass. The
  evaluator tree is byte-identical to `5ce71d1`, no relative links were added,
  production resource-limit assignments are unchanged, and the resource audit
  is clear. Checkpoint 5 remains reserved at 14 units,
  cumulative reserved use remains 52/70, 18 units remain unreserved, and
  Checkpoint 6 is not reserved. Independent semantic and final root review are
  still pending, so Checkpoint 5 is not marked complete.
- CP5 semantic review rejected `cf93de7` with two important authority gaps.
  The first focused RED,
  `nested_same_implementation_selections_keep_distinct_polymorphic_adapters`,
  selected one generic `Score<Option<A>>` implementation at two distinct
  evidence nodes but failed linked catalog construction with
  `InvalidEvidenceRoot`; the catalog had collapsed both nodes to one
  occurrence-and-implementation key. The second focused RED,
  `monomorphic_adapter_edges_reject_same_typed_wrong_producers_after_every_rebuild`,
  replaced one adapter prerequisite with a distinct same-typed producer while
  preserving the edge node, ordinal, type, and semantic producer tag;
  independent Core validation admitted the original tamper. These were local
  CP5 authority failures, not missing language or selection rules.
- The correction retains exact selection-node identity in every adapter row,
  expectation key, producer relation, Builder event, anchor, transform replay,
  and independent comparison. A nested `Score<Option<Option<Int>>>` witness
  now retains two adapters for the same `ImplMethodId` with distinct head
  substitutions, evaluates to 82, and freshly validates and evaluates after
  identity and literal folding. Adapter edges also retain their exact argument
  node and selection identity. Monomorphic abstract producers additionally
  retain the linked flattened position in the occurrence owner's evidence
  function envelope; validation derives the generated binder from the exact
  linked owner and Core initializer rather than trusting copied anchor data.
  Distinct `Base<Int>` and `Spare<Int>` requirements provide same-typed
  generated binders: swapping the argument alone or coordinating the argument,
  producer-node, and binder anchor is rejected before and after both
  transforms.
- Correction resource accounting charges the two occurrence-owner rows and
  each adapter selection identity before reserve/publication. The catalog
  boundary moves from 87 to 91 constraint units while type work remains 74.
  For the independent polymorphic fixture, `A = 3` and `Q = 2` add 28 exact
  matcher, role, detailed-edge, and prerequisite-sequence units, moving 2,219
  to 2,247. The monomorphic fixture's exact owner-envelope term is
  `N + R + p + 1 = 49 + 5 + 0 + 1 = 55` within its 701-unit boundary. Exact
  adapter-node lookup is exact. The replacement one-edge transform probe costs
  678 units for both identity and fold: 673 fixed reconstruction/Builder units,
  `X = 4` source-anchor traversal units, and `G = 1` exact producer-node remap
  unit. Every boundary has one-short rejection and fresh retry;
  semantic producer tampering is repeated after both transforms. The CP5
  reservation remains 14 units, cumulative reserved use remains 52/70, 18
  units remain unreserved, and Checkpoint 6 is not reserved. Semantic
  re-review and final root verification remain pending, so Checkpoint 5 is not
  marked complete.
- Correction verification passes 704 library tests, all 62 Core-validation
  integration tests, all 21 architecture tests, and the complete 1,511-test
  locked workspace/all-target/all-feature matrix. The nested-selection and
  monomorphic-producer focused tests pass after their final assertions. Locked
  all-target/all-feature checking, strict Clippy with warnings denied, `cargo
  xtask verify` including rustdoc, Markdown lint, and diff hygiene pass. The
  evaluator tree remains byte-identical to `5ce71d1`; no specification file or
  production resource-limit assignment changed. CP5 remains open for semantic
  re-review and final root verification.
- A second semantic re-review of `98000f7` found one remaining concrete-source
  authority gap. A polymorphic `Convert<Wrap<A>>::convert<X>` adapter selected
  the concrete monomorphic `Base<Int>` implementation, but independent Core
  validation trusted the copied edge producer node, tag, selection identity,
  and type. The focused RED coordinated those copied fields while replacing
  the selected source with a reachable same-typed ordinary global; validation
  admitted the original tamper before production changed. Existing linked
  selection and checked implementation-method facts completely determine the
  source, so no language, selection, or representation rule was added.
- The correction retains a bounded concrete-source catalog only for
  monomorphic implementation sources reachable from existing polymorphic
  adapter-edge expectations. Each row records the occurrence and selection
  node, exact `ImplMethodId`, checked binder, selected head arguments, and
  ordered prerequisite selection-node/method relation, including the exact
  enclosing evidence-function position for abstract prerequisites. It retains
  no Core `NodeId`. Independent validation now replays the canonical variable,
  exact head `TypeApplication`, and complete prerequisite `Apply` chain from
  those immutable facts. The coordinated same-typed global mutation rejects
  in original Core and after identity and literal-fold transforms.
- The general catalog probe moves from 91 to 101 constraint units because the
  bounded source pass performs two exact expectation passes, reserves its root
  worklist, and classifies the selected source; type work remains 74. The
  concrete-source catalog fixture is exactly 125 constraint and 36 type units,
  and its independent validator is exactly 588 units. Each has one-short
  rejection and two fresh exact retries. The 2,197 figure is the predecessor
  baseline inside the unchanged polymorphic authority probe; adding 22
  precharged capacity rows and 28 identity units gives that fixture's 2,247
  total. The earlier `cf93de7` transform fixture used 304/300 Core units plus
  three anchor reads for 307/303 total; `98000f7` replaced it with the
  concrete one-edge 678/678 fixture. Four exact concrete-source matcher lookups
  move that current identity/fold boundary to 682/682, with one-short failure,
  exact success, shared catalog `Arc`, fresh validation, and `Weak` teardown.
  Builder's isolated one-anchor boundary remains 14. The CP5 reservation
  remains 14 units, cumulative reserved use remains 52/70, 18 units remain
  unreserved, and Checkpoint 6 is not reserved. CP5 remains open for semantic
  re-review and final root verification.
- Second-correction verification passes 707 library tests, all 62
  Core-validation integration tests, all 21 architecture tests, and the
  complete 1,514-test quiet locked workspace/all-target/all-feature matrix.
  The broader locked workspace/all-feature run also passes. Formatting,
  locked all-target/all-feature checking, strict Clippy with warnings denied,
  `cargo xtask verify` including rustdoc, Markdown lint, and diff hygiene pass.
  The evaluator tree remains byte-identical to `5ce71d1`; no specification file
  or production resource-limit assignment changed. CP5 remains open for
  semantic re-review and final root verification.
- Quality and resource review of `5c6af3d` found four remaining accounting
  defects. The focused constructor RED,
  `method_evidence_builder_constructor_precharges_both_exact_carriers`,
  measured two units for `E = 2` expectations where the consumed bitmap and
  anchor carrier require four. The correction stages both exact-capacity
  buffers after a checked `2E` charge and publishes them atomically. Catalog,
  lowering, and validator parameter carriers now charge before reserve;
  checked type walkers separately charge every root and child stack slot.
  Catalog expectation, implementation-method, interface-method, owner, and
  scheme searches either precharge each count and search pass or fuse them
  into charge-before-compare traversal. The fused global-scheme lookup
  preserves the unchanged wide-interface default-budget boundary. Concrete
  source validation additionally charges the complete abstract prerequisite
  method list before membership.
- Exact CP5 accounting after the review is four units for the isolated `E = 2`
  Builder constructor, while the distinct one-anchor authentication and finish
  boundary remains 14. General catalog construction is 105 constraint and 74
  type units; the concrete-source fixture is 140 constraint and 36 type units.
  The zero-prerequisite concrete validator moves from 588 to 633 units after
  45 checked stack-capacity slots, and the polymorphic validator moves from
  2,247 to 2,339 after 92 such slots. A reachable concrete source with two
  retained methods from one abstract prerequisite is exactly 1,088 units; its
  explicit authorization term is `Q * W = 2 * 2`. The isolated lowering
  worklist is ten units for five visits plus five capacities. The concrete
  one-edge identity and literal-fold transforms move from 682 to 686 units
  because their `E = 4` catalog now charges both constructor carriers. Every
  boundary rejects one-short work and succeeds on two fresh exact retries.
  No production resource limit changed.
- Post-review verification passes 710 library tests, all 62 Core-validation
  integration tests, all 21 architecture tests, and the complete 1,517-test
  quiet locked workspace/all-target/all-feature matrix. Formatting, locked
  workspace/all-target/all-feature checking, strict Clippy with warnings
  denied, `cargo xtask verify` including rustdoc, Markdown lint, relative-link
  verification, and diff hygiene pass. The evaluator tree remains
  byte-identical to `5ce71d1`; no specification file or production
  resource-limit assignment changed. The CP5 reservation remains 14 units,
  cumulative reserved use remains 52/70, 18 units remain unreserved, and
  Checkpoint 6 is not reserved. CP5 remains open for review and final root
  verification.
- Final quality re-review of `8eccef4` found one localized catalog-metering
  gap: two root producer lookups charged domains and adapters but not the
  selected evidence node's method width, and two prerequisite counts inspected
  their child rows before charging the count pass. The correction charges the
  exact root method width before each producer lookup. Concrete-source and
  adapter-edge prerequisite counts now charge the prerequisite rows before
  reading children, then charge the derived method-edge capacity before
  reserve. The already-budgeted sibling semantic-producer path is unchanged.
- A reachable abstract-only witness retains `W = 2` selected methods, `D = 2`
  domains, `A = 0` adapters, and two producer lookups. Its exact catalog
  boundary is 89 constraint and 32 type units: 85 fixed units plus
  `L * W = 2 * 2`. General catalog construction moves from 105 to 107
  constraint units while type work remains 74; concrete-source construction
  moves from 140 to 141 while type work remains 36. Both new and revised
  boundaries reject one-short work and succeed on two fresh retries. The
  approved Builder 4/14, validator 633/1,088/2,339, transform 686, and
  elaborator 10 boundaries remain unchanged. No production limit changed.
- Final-review verification passes 711 library tests, all 62 Core-validation
  integration tests, all 21 architecture tests, and the complete 1,518-test
  quiet locked workspace/all-target/all-feature matrix. Formatting, locked
  workspace/all-target/all-feature checking, and strict Clippy with warnings
  denied pass, as do `cargo xtask verify` including rustdoc, Markdown lint,
  relative-link verification, and diff hygiene. The evaluator tree remains
  byte-identical to `5ce71d1`; no specification file or production
  resource-limit assignment changed. The CP5 reservation remains 14 units,
  cumulative reserved use remains 52/70, 18 units remain unreserved, and
  Checkpoint 6 is not reserved. CP5 remains open for review and final root
  verification.
- Independent semantic re-review approves the complete CP5 meaning with no
  findings. It confirms exact selection-node identity for repeated adapters,
  owner-envelope derivation for abstract monomorphic sources, and independent
  reconstruction of concrete monomorphic sources from linked selection and
  checked implementation facts. Builder consumption, transform remapping, and
  fresh validation preserve those relations. The later corrections change
  only resource charging, traversal shape, exact probes, and task evidence;
  they add no Core form, evaluator behavior, selection rule, language rule, or
  specification change.
- Independent quality and resource re-review approves `600ba23` with no
  findings. It verifies that both root producer callers precharge checked
  `D + A + W`, prerequisite rows are charged before child inspection, and
  derived method-edge capacity is charged before reserve. The 89/32,
  107/74, and 141/36 catalog boundaries and the approved Builder 4/14,
  validator 633/1,088/2,339, transform 686, and elaborator 10 boundaries pass
  exact, one-short, and two-fresh-retry evidence. Lifecycle, iterative
  teardown, `Arc` identity and `Weak` release, architecture carriers,
  evaluator isolation, checked arithmetic, and unchanged production limits
  also pass. Checkpoint 6 retains only its planned product-level exhaustive
  coverage.
- Fresh root verification at `600ba23` passes the four corrected exact
  resource probes, eight method-evidence unit tests, all 711 library tests,
  all 62 Core-validation tests, all 33 interface tests, all 40 polymorphism
  tests, and all 21 architecture tests. The locked
  workspace/all-target/all-feature run and its exact test listing pass all
  1,518 tests. Formatting, locked workspace/all-target/all-feature checking,
  strict Clippy with warnings denied, `cargo xtask verify` including rustdoc,
  Markdown lint, relative-link and authority review, cumulative diff hygiene,
  evaluator and specification byte identity against `5ce71d1`, exact-head
  inspection, and clean-worktree status pass. Checkpoint 5 is complete in
  `cf93de7`, `98000f7`, `5c6af3d`, `8eccef4`, and `600ba23`. Its reserved use
  is 14 units, cumulative reserved use is 52/70, 18 units remain unreserved,
  and Checkpoint 6 is not reserved.
- Checkpoint 6 starts from the clean reviewed boundary `851c26c` and reserves
  its planned 10 units for the complete linked product, behavior and exclusion
  evidence, exact diagnostics and migration, and exhaustive carrier, resource,
  retry, and disposal evidence. Cumulative reserved use is 62/70, eight units
  remain unreserved for Checkpoint 7, and Checkpoint 7 is not reserved. This
  reservation does not authorize specification changes, production resource
  limit changes, new evaluator state or behavior, new Core forms, selection
  changes, or a new language rule.
- The complete product RED first lacked its retained three-module fixture and
  resource target. Once those existed, it exposed two earlier-checkpoint
  authentication defects. Imported checked method facts retained the whole
  declaration span instead of the exact annotation subspan, so linked
  implementation evidence could not reconstruct the selected interface-method
  identity. Retaining and authenticating that copy-only span closes the gap.
  Full cross-module implementation provenance then reached Core, whose accepted
  invariant permits only source-local related spans. Linked validation still
  authenticates the complete cross-module origin; final Core lowering projects
  its already-authenticated primary span. Core validation, evaluator behavior,
  and every source provenance carrier remain unchanged.
- The retained `Functor<F>.map<A, B>` product uses unrelated `Int`-to-`Bool`
  and `Bool`-to-`Int` instantiations inside one separately checked constrained
  global, a generic `Box<A>` implementation, and explicit entry-module
  selection. The same source fixture evaluates to
  `(Box(true), Box(42)) : (Box<Bool>, Box<Int>)` through the library and CLI.
  Its original, identity-transformed, and folded Core programs independently
  validate and evaluate equally. Exact evidence-node traces and an exhaustive
  runtime-carrier inventory retain only existing type erasure, lookup, and
  application transitions; no evaluator value, environment entry, frame,
  lookup class, failure, or runtime interface state was added.
- Diagnostic and migration evidence covers all twelve unavailable higher-rank
  routes, exact typed reasons and spans, failure precedence, the absent-list
  predecessor rejection, and the explicit-list accepted migration through both
  library and CLI paths. Because `interface` is a reserved module token, the
  mandated retained `interface.ash` and `implementation.ash` sources are staged
  as `api.ash` and `carrier.ash`; their contents and the retained `entry.ash`
  remain the one product fixture used by both paths.
- Resource evidence retains the exact syntax formula `66 + 14P` at
  `P = 1, 2, 3, 512` and a bidirectional manifest for all syntax, resolved,
  summary, linked, adapter, Core, transform, and teardown carriers. Its 27
  unique owner probes include exact selector, publication, rigidity,
  conditional, evidence-scope, catalog, Builder, validator, worklist,
  transform, discarded-buffer, and pending-zonk formulas. Deep accepted and
  rejected depth 96, wide accepted and rejected width 128, width-64 adapter
  transforms, a prebuilt rejected adapter-bearing Core program, and pending
  zonk teardown all dispose on a 256 KiB stack. Public width 1,024 succeeds;
  width 5,000 fails twice at the unchanged typing constraint budget and a fresh
  width-1,024 retry succeeds.
- The complete public adapter pipeline cannot be constructed on a 256 KiB
  stack even at width two because of a width-independent construction frame.
  That boundary is intentionally excluded from the teardown claim: retained
  small-stack evidence consumes prebuilt accepted and rejected adapter states.
  It is not a teardown defect, semantic gap, or reason to change a production
  limit.
- Independent semantic review approves exact binder authority, linked
  provenance authentication before source-local Core projection, shared
  product observations, transform revalidation, runtime erasure, diagnostics,
  migration, and exclusions with no findings. Independent quality and resource
  review first rejected an incomplete formula manifest, a one-way carrier
  inventory, and insufficient rejected-lifecycle evidence. The same
  implementation pass added the complete formulas, bidirectional inventories,
  prebuilt rejected-Core disposal, and the two omitted hidden-import and
  discarded-head-buffer probes. Re-review approves the corrected boundary with
  no findings.
- Fresh root verification passes all 711 library tests, 62 Core-validation
  tests, 34 interface tests, 41 polymorphism tests, 23 architecture tests, and
  the combined 240-test Checkpoint 6 focus. The locked
  workspace/all-target/all-feature run and exact listing pass all 1,531 tests.
  Formatting, locked checking, strict Clippy with warnings denied,
  `cargo xtask verify` including warning-denied rustdoc, Markdown lint, all
  relative-link targets in 84 Markdown files, and diff hygiene pass. The
  specification, evaluator, Core validator, and production limits remain
  unchanged. Checkpoint 6 is complete in `dab6e93`; its reserved use is ten
  units, cumulative reserved use is 62/70, eight units remain unreserved, and
  Checkpoint 7 is not reserved.

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

A body-free checked interface-method fact must retain the exact annotation
subspan. The whole declaration span is insufficient to reconstruct and
authenticate imported implementation provenance.

Cross-module related spans belong to linked evidence, where source identities
are available for authentication. After that check, Core receives the
source-local primary span required by its existing provenance invariant.

Small-stack teardown evidence may consume prebuilt states when a
width-independent construction frame exceeds the target stack. The retained
claim must name that construction exclusion and separately cover both accepted
and rejected lifecycle states.

## Deviations

No deviation from CP-0010 is currently known. Any product evidence that exposes
missing or incorrect semantics returns to proposal or design work instead of
being decided in this task.
