# TASK-0027: Implement Safe Resource Scope

- ID: `TASK-0027`
- Status: active
- Related: [CP-0017](../proposals/CP-0017-safe-non-foreign-resource-scope.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [execution plan](../plans/2026-09-06-safe-resource-scope.md)

> This task organizes authorized work; CP-0017 owns the semantic transition.

## Dependencies

Baseline: `387c4eff925d1d4fdbad08c3eb3c02028bb01035`, the locally integrated
capture/discard checkpoint. Its full gate passed 2,156 tests; integration
revalidation passed 1,153 tests. Recheck the baseline before product edits.
The user approved scope-owned release with reusable cell access on 2026-09-06.

## Work

Implement CP-0017 using one product writer at a time, test-first bounded
increments, semantic review followed by Rust/resource review, and final
documentation verification. Use high reasoning for compiler/runtime and
semantic/resource reviews, medium for mechanical documentation work; never
exceed high. Keep commits unsigned per the user's instruction. Use the local
`.worktree/safe-resource-scope` checkout and retain local integration only.

## Progress

- Read-only semantic and implementation-boundary audits completed.
- The user approved the concrete resource contract after those audits.
- Moved the clean integration checkout to the active feature worktree and
  created `codex/safe-resource-scope`; integration remains at the baseline.
- Fresh full baseline verification passed before product changes.
- Accepted proposal, task and implementation plan recorded.
- Independent contract review required explicit owner-relative checking of
  dependent request payloads sent to outer handler clauses. CP-0017 now records
  that rule and the copied-payload/live-outer controls; no temporary lending
  discipline is introduced.
- The reviewer confirmed that the revised contract closes the reported gap.
- Moving the worktree exposed stale executable paths in Cargo's retained
  package cache. Rebuilding that cache restored all 74 specification-example
  tests without changing source or tests. The fresh full baseline gate then
  passed with `CARGO_INCREMENTAL=0 cargo xtask verify`: 2,156 tests in 62
  binaries plus formatting, metadata, build, Clippy and rustdoc.
- Step 1's first frozen revision passed 1,094 focused tests, all-target Clippy
  with warnings denied, and formatting. Review corrections are in progress;
  no resource acquisition code has been implemented yet.
- The full Step 1 gate passed build/lint and library tests, then exposed missing
  architecture-inventory entries and raw mutation of an iterative owner. Four
  inventory entries and the narrow owner-method correction now pass their exact
  architecture checks. Semantic re-review closed the empty-row finding; the
  corrected focused suite passed 1,097 tests plus Clippy and formatting.
- Rust/resource review found one charge-before-staging omission in the shared
  type/row substitution helper newly used by runtime instantiation. The bounded
  correction passed 1,101 focused tests, Clippy and formatting. Independent
  resource re-review closed the finding with five targeted tests.
- The next full gate passed all 32 architecture checks, then aborted on a stack
  overflow in `data_and_adts`. The same compiled test binary passes all 32 tests
  serially but reproduces the abort with normal concurrency. The isolated
  synthesized-type-wrapper test also aborts alone on its 256 KiB thread stack;
  its trace shows accumulated elaboration frames, not recursive traversal.
  A fresh baseline build passes that test; the current revision fails it. The
  driver's frame grew by 96 bytes through its later inline Effect phase.
  The narrow phase-helper extraction reduces that frame by 17,728 bytes. Its
  fresh-process regression went RED to GREEN without changing the stack limit
  or concurrency. Independent review closed the correction; 1,133 focused tests,
  Clippy and formatting passed.
- Step 1's fresh complete gate passed: `CARGO_INCREMENTAL=0 cargo xtask verify`,
  2,183 tests in 62 binaries plus formatting, metadata, build, Clippy and rustdoc.
  Both independent reviews are closed. Documentation review corrected three
  stale erasure/frame statements; seven affected documents pass Markdown lint
  with the line-length exception for existing formal rules/tables, and 29 local
  link targets were checked. Step 1 is retained in unsigned commit `8810a44`.
- Step 2's first three module tests reproduced the missing builtin import,
  unknown builtin path and reserved-root preflight behavior.
- The fixed API parsed and resolved, then reproduced an existing export-freezing
  failure for public effectful methods. Identical filesystem source also fails.
  The paired type comparison in `InterfaceConstraintBudget::charge_equal_types`
  omits `EffectfulFunction` and rejects matching signatures. Step 2 includes the
  narrow structural repair and its exact-work/row-identity controls.
- After that repair, importing the ordinary API reproduces a second omission:
  summary admission checks operation value kinds before registering the nominal
  kinds those operations use. Step 2 moves those kind checks after registration,
  preserving the earlier parameter-identity checks and malformed-fact rejection.
- Step 2 now admits the fixed builtin through ordinary parsing and checking,
  preserves its origin through targeted/facade imports, rejects source provider
  introduction and ordinary handle construction, and projects resource syntax.
  A direct targeted import of only `Handle` satisfies the acquisition dependency
  check; facade-only access does not. Acquisition still rejects before resolved
  publication; this is not an executable resource checkpoint.
- The frozen Step 2 revision passed the parent's focused gate: 1,123
  tests in 11 binaries, covering library, resource syntax/modules, CLI, module
  loading/resolution/visibility/elaboration and existing Effect Core/modules.
  The fresh-process 256 KiB wrapper regression also passed.
- Semantic review closed without actionable findings. Independent CLI probes
  also passed imported constrained forwarding and method-only facade use, and
  distinguished direct method-only acquisition availability from facade-only
  access. Rust/resource review also closed without actionable findings; its
  eight targeted equality/builtin checks passed. All 32 architecture checks have
  passing evidence: the final unchanged ownership scanner passed after the
  test helper used `pop` followed by immediate iterative disposal. Parent
  all-target Clippy, formatting, Markdown lint and diff checks passed.
- Step 2 is retained in unsigned commit `0ae5203`. The worktree was clean after
  the commit; main and integration refs are unchanged.
- Step 3 is active with one high-reasoning product writer. It adds acquisition
  typing and independently checked Core authority. Stored-dependency analysis
  and runtime execution remain later steps; executable resource admission must
  stay closed until their required checks exist.
- Step 3's six initial source test groups reproduce the existing resolution
  rejection. The selected boundary scopes the rigid identity and handle over
  the body only, reuses lexical evidence selection with a distinct acquisition
  origin, and leaves source `with` eligibility unchanged. Typed structure gets
  internal positive controls; production checked-module publication remains
  explicitly unavailable until stored-dependency analysis exists. No persisted
  proof-status carrier or unchecked public success API is introduced.
- Step 3 reached its first compiling boundary. Direct/helper and targeted
  acquisition cases reach the later publication guard after typing; unrelated
  provider requirements and exposed-handle escape reject earlier. Initial test
  expectations were corrected to the ordinary argument diagnostic and the
  transitional publication guard, and the malformed closure fixture was
  corrected. The parent's rerun passed all six source groups. A new
  fresh-process test of 24 nested acquisitions on a 256 KiB stack aborts.
  The trace locates the failure in the second elaboration-driver frame, entered
  by the new resource initializer path after loading and resolution completed.
  The correction schedules resource initializer/body/finish work on the existing
  task driver, without changing stack or depth limits. The writer's internal
  typed-structure controls pass direct read and distinct nested initializer/body
  effect instances. Core ownership and adversarial checks remain in progress.
- Loop-driven resource scheduling removed the first recursive driver path.
  The unchanged stack witness then reached the existing `perform` operand
  check and overflowed on its recursive driver call. The second trace confirms
  that path. Step 3 includes the narrow operand/check/finish scheduling repair
  with ordinary `perform` controls; signature, diagnostic, row, result and
  handler behavior are preserved. No stack or syntax limit is raised.
- The unchanged 24-acquisition fresh-process witness passed after both scheduling
  corrections; the parent independently reran it at 256 KiB. Temporary phase
  prints were removed. The complete Core fixture checks both provider owners
  and their exact generated requests. Identity and folding transformations
  independently reach the same explicit proof-unavailable guard; their private
  test fixture is never evaluated and creates no production admission path.
- The Step 3 library gate passed all 1,033 tests. Its escape scan exposed one
  reused helper that counted effect arguments before charging nullary label
  width. The narrow precharge correction has exact/one-short/retry evidence.
  Focused integration, ownership and lint gates remain in progress, followed by
  independent semantic and Rust/resource reviews. Step 3 is not yet frozen.
- The focused helper/facade test exposed an import-route defect even without
  acquisition. The direct route retains `Handle` with opaque access; the helper's
  hidden closure retains identical defining metadata with hidden access. The
  closure comparator incorrectly rejects the latter when the former arrived
  first. Step 3 includes the narrow separation of route access from canonical
  closure equality, without changing name visibility or access merging.
- A private fixture now exercises the actual linked resource/header traversal:
  the authentic body passes, while detached or initializer-moved evidence,
  changed acquisition ownership and a missing body identity reject. The same
  check has exact/one-short/retry evidence. It constructs no resource-bearing
  `CheckedModule` and does not bypass production publication. Full publication,
  linking and surplus-owner integration remain explicit Step 4 gates.
- Step 3 is frozen for semantic review. The writer's final gate passed 1,034
  library tests and 344 tests across 21 integration binaries. The parent's
  independent gate passed 1,137 tests across 11 binaries. Both fresh-process
  256 KiB controls pass, as do parent all-target Clippy and diff checks.
  Architecture evidence consists of the earlier full 32 checks and a current
  31-check refresh; the unchanged ownership-mutation test is not rerun in that
  refresh. No lifetime or execution support is claimed by this checkpoint.
- Semantic review found one diagnostic defect: immediate resource escape points
  at the whole acquisition, and both immediate and deferred errors omit the
  known acquisition label. The parent reproduced it with the compiled CLI.
  The sole writer is correcting primary/related spans with direct, latent-row
  and deferred controls. Invalid body typing still takes precedence; no separate
  precedence or authority defect was established. Re-review is required.
- Direct-result and deferred label corrections passed re-review. The same
  finding remains for an immediate outward effect row: an earlier `Escape<R>`
  request is incorrectly attributed to the body's final resource-free literal.
  Separate the value-result location from the outward body-computation location;
  no general provenance analysis is needed. Add that row-specific regression.
- Semantic re-review closed all findings after the immediate-row correction.
  The parent's fresh corrected-revision gate passed 1,212 tests in 13 binaries,
  and workspace all-target Clippy passed. Rust/resource review is active; the
  product revision remains frozen. Step 3 is not committed yet.
- Rust/resource review found two raw deep-type clones retained across new
  fallible operations: the scheduled `perform` domain and the resource result's
  Core type. Both need the existing iterative owner until transfer. The reviewer
  established the deterministic work-exhaustion paths but did not claim a newly
  reproduced stack overflow. The writer is adding guarded ownership and deep,
  small-stack exhaustion/retry controls. No broader predecessor cleanup is
  included; resource re-review is required.
- Resource re-review closed both ownership findings. Existing test-only disposal
  counters observed the missing 513-cell domain and 259-cell result before the
  guards; unchanged exhaustion and fresh exact retries pass on 256 KiB workers.
  The resource fixture remains within the existing Core payload-depth limit.
  The final parent gate passed 1,214 tests in 13 binaries, workspace all-target
  Clippy, and the fresh Pure stack regression. Both independent reviews are
  closed. Step 3 is complete within its explicit structural boundary, with
  production resource publication and execution still unavailable.
- Step 3 is retained in unsigned commit `64647d8`; the worktree was clean after
  that commit. Main and integration refs are unchanged. A fresh high-reasoning
  writer is starting Step 4 with stored-dependency and scope-obligation analysis.
  It will first identify the smallest extension to existing value summaries and
  control, then begin the paired escape/acceptance regressions. Runtime cells
  remain Step 5.
- Step 4's initial stored-closure witness reproduced the missing dependency
  check. The writer's 15-test source gate now covers direct hidden captures,
  generic forwarding, closure factories and identity-only effect metadata,
  paired with copied integers and constant closures. Publication remains closed;
  field projection, request transfer and scope completion are still in progress.
- The writer's later 22-test source gate covers owner-relative request transfer,
  outward abandonment, safe inner discard, skipped scope completion and recursive
  resource occurrences. The 70 predecessor capture/effect tests pass again after
  restoring empty-carrier copy-cost locality. Independent final Core now runs
  resource analysis before the execution guard: a well-typed hidden-closure
  witness changes from proof-unavailable to resource-escape. Seven focused Core
  checks pass. The complete value-graph refinement and publication proof remain
  unfinished; these are intermediate writer gates, not final reviews.
- The contextual request/resume pair now distinguishes a hidden dependent
  closure from a constant closure. Imported generic projections, factory call
  separation, metadata-row captures and pure import execution also have passing
  writer evidence. The joint analysis initially exhausted the existing work
  limit on the 24-nested-scope test. Phase measurements located repeated full
  value-graph scans before control discovery. A dependent-slot worklist restored
  the 32-test resource suite without raising limits; the predecessor capture
  suite also passed 15 tests. A stronger new request-payload test remains RED:
  an imported projection after a cell read reaches the publication guard instead
  of reporting its hidden dependency. The writer is tracing that reachability
  gap. Publication, execution, final reviews and the Step 4 commit remain pending.
- The imported-payload pair then went RED to GREEN. Correctly exposing external
  methods as opaque revealed excessive control exploration in two valid cases
  (31 of 33 source tests pass). Source checking already builds selected lexical
  method bodies, but capture analysis sees shared method placeholders. A bounded
  read-only review identified per-occurrence staged evidence as the missing
  relationship; connecting it must preserve the existing audit and atomic
  publication gates. The separate effectful-pattern prerequisite now has a
  passing resource-free tuple relay and 29 passing pattern tests, including
  Pure rejection and exact-work/retry controls. The parent independently reran
  those 29 compiled tests; final increment verification remains pending.
- The direct selected-method bridge passed a 35-test resource checkpoint, also
  independently rerun by the parent. Subsequent disjoint-selection and imported
  constrained-helper tests pass. A used-versus-unused prerequisite pair exposed
  over-retention of supplied methods; inert occurrence specialization now passes
  that pair, including a nested imported wrapper. The parent independently
  reran all three evidence-focused tests successfully. The recursive inherited
  payload test still fails with `ResourceEscape`, as independently reproduced;
  its owner-provenance refinement remains unfinished. The writer's 56-test
  predecessor effect gate passes. Implementation-method summary retention and
  exact prerequisite adapters are the next active source-analysis changes.
- Implementation method facts now retain the existing private capture summary.
  Direct and nested selected prerequisite adapters passed the six-case
  hidden/copy/constant test, independently rerun by the parent. A separate
  imported adapter chain with a method-local type parameter also distinguishes
  hidden capture from copied and constant results in parent CLI probes. A
  resource-free implementation-only import still executes 42. These are
  intermediate checks: the recursive-owner regression, publication and execution
  guards, and final increment reviews remain open. Bounded review identified a
  missing post-staging capture-failure atomicity test; the existing module-failure
  test fails before evidence staging. The ownership scanner also reports five
  new fields awaiting inventory entries, with no stale entries.
- The parent reran the expanded resource suite: 40 tests and the nested-stack
  child pass, explicitly excluding the known recursive-owner regression. Actual
  execution of the method-local nested adapter chain exposed a separate baseline
  defect: Pure and Effect Core both reject with `ApplicationType`, reproduced
  on the exact `64647d8` archive. The passing Pure control above uses the simpler
  adapter, not this chain. GDB locates the failure in concrete prerequisite
  validation: a global method-catalog entry selects an anchored representation
  check even though this occurrence retains a concrete child source. Bounded
  diagnosis is in progress; the original chain execution remains a required
  regression, not an excluded unsupported form.
- The post-staging method-only failure test now passes independently: the later
  resource escape leaves the earlier selection private, and a fresh corrected
  module publishes distinct method summaries. The five-test publication gate
  and the older pre-staging module-failure test also pass. Independent diagnosis
  confirmed that Core must distinguish method-level polymorphism, as lowering
  already does. The one-predicate correction now executes both original Pure
  and Effect adapter chains with result 42 in parent CLI runs. Tampering,
  transformed-Core and exact-budget regression checks remain in progress;
  recursive-owner refinement and whole-increment closure remain unfinished.
- The parent reran the concrete-source, exact-budget and tampering gates
  successfully, including the new nested monomorphic leaf test. The rebuilt
  ownership scanner now passes its exact fixed-point check. The broader gate
  then aborted in the existing 64 KiB capture-equation test; the parent reproduced
  that test's stack overflow independently. GDB identifies the enlarged
  `Graph::build` entry frame, not recursive traversal. The writer is extracting
  sequential construction phases without changing the stack or work limits.
  No whole-library or whole-increment pass is claimed.
- Sequential graph-construction phase extraction restores the exact 64 KiB
  regression; the parent independently reran it successfully. The writer is
  rerunning the library gate before owner refinement. Restored owner analysis
  will distinguish static continuation cuts as well as old contexts, preserving
  completed child values and lexical captures while keeping pending result
  ports active. The original and restored recursive-owner regressions remain
  required; no focused-owner implementation is complete yet.
- The full library rerun completed with 1,040 passes and four failures in budget
  tests. Duplicate-route tests now account for retained-summary comparison work
  while preserving their exact constraint totals and unchanged-state checks;
  the parent reran the 36-test duplicate gate successfully. The cumulative
  module-budget test also passes independently with one measured complete-module
  budget. The exact `64647d8` archive passes its original cross-stage snapshot.
  The new snapshot adds 90 units in each of four dependent resolution stages:
  18 retained nominal re-admissions per importer, each charging five units.
  Checking, linking and linked-evidence validation contributions are unchanged.
  The parent independently reran the corrected exact/one-short/fresh-retry test;
  the writer's full library run then passed all 1,044 tests.
- A retained nested-handler callback fixture exposes an ordinary predecessor
  defect, also reproduced without resources on `64647d8`. Enclosing-clause row
  recomputation reads a stored function type with a solved inference argument,
  then cannot remove the nested handler's rigid effect instance exactly.
  Bounded review confirms non-strict normalization of the handler's emitted
  Core suffix and output row before recomputation. Exact effect matching stays
  unchanged; failure must propagate through the existing poison/discard owner.
  The parent independently reran the resource-free execution, wrong-instance
  rejection, hidden/copy/constant callback and exact row-recompute tests
  successfully. The parent also reran normalization exhaustion/fresh-owner retry
  and both strengthened nested concrete-source validation tests successfully.
  The writer's post-normalization library run passes all 1,045 tests; the
  non-owner resource source gate passes 44 tests and its small-stack child.
  No same-builder retry or whole-Step-4 completion is claimed.
- The parent added a completed-function-before-suspending-argument probe for
  owner restoration. Its resource-free predecessor executes 42 on both the
  feature executable and exact `64647d8`. With an ordinary term capture, the
  safe resource variant reaches the old publication guard on `64647d8`, but
  the feature analysis returns an internal error while popping an unconsumed
  clause. The paired resource-dependent result must reject. Bounded diagnosis
  identifies an older copied resource prefix sharing its address with the
  original prefix: both consumed and live clause tails become reachable.
  Rebound-prefix provenance must stay distinct without rewriting references to
  the original live prefix. Removing recursion gives the expected safe/unsafe
  pair; neither ignoring clause consumption nor weakening owner checks is an
  admitted correction.
- Focused-owner support now has two independently passing helper tests:
  static free-input subtraction and frozen completed-value creation slots.
  These helpers are not yet a wired owner proof. The parent independently ran
  the compiled library gate (1,047 passes) and non-owner source gate (44 passes
  plus its small-stack child). The retained recursive-owner test still rejects
  its safe inherited value and remains an explicit failure.
- The first complete focused-owner query compiles. It collects acquisition
  entries, waits for joint convergence, marks the designated resource frame,
  and restores explicit result ports separately from saved lexical captures.
  The parent reran the non-owner source gate successfully (44 tests plus its
  small-stack child). The original recursive-owner pair now reaches type-work
  exhaustion on its inherited case instead of the earlier false escape; the
  writer reports that the local case still rejects escape. The exhaustion
  trace reaches control-state copying during a focused discovery pass, not
  normal data closure. Separate entry queries each converge, but continue
  through the outer program after their marked owner exits. Stop those paths
  at the marked frame's exit while retaining post-convergence body/result
  checks and all live-owner seeds. No default limit changed and neither
  publication guard opened.
- Stopping at owner exit saves little of the repeated traversal cost. The
  bounded scheduling review identifies calls as the control transitions whose
  successors depend on growing value facts. The implementation now retains
  exact visited states, replays reached calls (including bottom targets), and
  defers all recorded payload-crossing obligations until convergence. The
  parent reran the 44-test non-owner source gate and its small-stack child
  successfully. The inherited case covers more candidate entries but still
  exhausts the unchanged limit. A measured linear scan through unrelated value
  contexts is the next bounded target; an exact context index must preserve
  existing identity, folding and seed separation.
- The exact context index passes its narrow/wide and exact/one-short/fresh-retry
  test. The original recursive-owner pair now passes under the unchanged limit;
  the parent independently ran all 46 source tests and their small-stack child
  at that checkpoint. The direct older-prefix regression also passes: consuming
  a selected older clause uses a separate fixed completion region while
  original references retain their live clause.
- The restored recursive-owner pair still exhausted work after indexing. The
  parent trace locates repeated normalization of unchanged stack/heap pairs on
  call successors. Bounded review permits the existing enqueue tail for call
  targets, choice children and final sequence children that push no frame;
  stack or heap mutation still requires normalization. That correction admits
  the unchanged restored pair. The parent reran 47 source tests and their
  small-stack child, excluding one retained completed-factory failure.
- The completed-factory regression now reaches false resource escape instead
  of an internal control error. Its frozen pre-entry function is preserved;
  older control addresses instead join distinct already-known contexts and
  select a descendant clause as the outer resume owner. Review is checking
  a finite allocation-context partition, without treating context equality as
  owner equality or suppressing selected data edges. This remains open; no
  whole-Step-4 completion, publication admission or runtime support is claimed.
- Bounded review selected an immutable allocation-context component on every
  control address, using existing finite value-context IDs. Fresh clause
  addresses use their dispatch context; copies, consumption and restoration
  preserve source allocation provenance. This separates known contexts without
  inventing dynamic owner equality or distinguishing already-folded calls.
  The implementation is under test.
- The parent independently verified scalar-successor enqueue equivalence and
  closed-input final dependency checking. A broader capture gate reproduced a
  64 KiB stack overflow from the enlarged analysis local sharing a caller frame
  with graph construction. Extracting the final control-query phase fixes that
  unchanged test; the parent then passed all 22 capture tests. Allocation-context
  source verification and whole-increment review remain pending.
- Allocation-context partitioning changes the completed-factory failure to
  type-work exhaustion. It also regresses the original and restored inherited
  owner controls to exhaustion: the source gate passes 45 of 47 tests with the
  completed-factory test excluded. Earlier passing counts describe earlier
  revisions, not this one. The work limit remains unchanged.
- The cost trace shows several completed focused queries exhausting the
  cumulative ledger, rather than one nonterminating query. Skipping redundant
  sorting after a stack pop preserves reachability pruning; the parent passed
  its differential exact/one-short/fresh-retry test. That optimization alone
  does not admit the completed-factory witness. Bounded review is assessing
  coarse allocation addresses during candidate discovery with precise finite
  addresses in focused checks; no such phase-local change is implemented yet.
- The parent's post-sorting source rerun improves to 46 of 47: the original
  inherited-owner pair passes again; restored ownership still exhausts, with
  the completed-factory test excluded. The current 24-test capture gate also
  passes independently. Review holds phase-local address coarsening because
  recent-address replacement needs a singleton invariant across segment copies.
  The next bounded optimization reuses fully prepared identical static cuts
  within a focused query, preserving all later result-port joins.
- Prepared-cut reuse passes the parent's cache-hit/late-result-edge test, but
  restored ownership and the completed factory still exhaust. Initial cache
  publication needs its own measured boundary coverage. The combined sorting
  and cut-reuse trace moves the sixth factory query's start from 324,435 to
  295,180 charged type-work units; that is compiler work, not milestone effort.
- The address review also identifies a current domain invariant to check:
  copying different source regions into one region can merge distinct recent
  addresses with the same site/context. Such a destination must not claim to
  denote one occurrence. A source-level unconsumed-clause omission has not been
  reproduced; a direct copy-state regression remains required.
- A read-only consolidation map distinguishes redundant legacy resource proof
  from callable-target propagation. Remove stored/captured-parameter dependency
  state and the request-payload fallback, but retain returned-parameter target
  substitution for resource-free helpers. Contextual resource analysis must
  reject missing data or request ports, not fall back or silently succeed.
- The parent now passes initial prepared-cut publication and the complete
  cache-hit/late-edge path at their separate exact/one-short/fresh-retry
  boundaries. The complete source checkpoint passes 46 of 48 tests; restored
  ownership and the completed factory remain type-work exhaustion failures.
  The factory has seven retained entries and two candidate keys. Five focused
  checks finish, the sixth exhausts, and the seventh remains unvisited.
- A direct mixed-region copy test reproduces the recent-address collision.
  Tracking distinct source addresses per copy destination and marking collided
  destinations as older passes the parent's regression, including duplicate
  same-source edges and older-tail union. Bounded review accepts this narrow
  correction. Explicit existing-recent aging coverage and charge-before-staging
  verification are being added before legacy dependency consolidation.
- The copy helper now charges before staging its maps, and the regression
  covers aging an existing recent destination while preserving older tails.
  Legacy `Value.stored`, `captured_parameters`, resource handle-taint scans,
  `Request.payload` and its fallback check are removed. Returned-argument
  callable targets remain; metadata extraction uses a separate charged
  variable set. The parent passes all 27 capture tests after this consolidation,
  including the unchanged small-stack and exact-work boundaries. Missing
  contextual-data/port negatives and fresh source verification remain pending.
- The parent's fresh consolidated source run remains 46 of 48. The new
  missing-context and wide-copy preflight tests pass independently, including
  zero/one-short/exact/retry copy budgets. Coverage with contextual data present
  but its request port missing is still being checked. The returned-generic-
  callable discard controls are retained as a resource-free predecessor pair.
- Bounded review supports skipping replay only for an already-expanded exact
  call state whose target/context set and unknown/normal-return flags have not
  changed. New control states still expand once, and joint value convergence
  and downstream calls remain mandatory. Measure the existing repeated work
  before changing scheduling; retain all seven factory entry checks.
- The parent passes the expanded present-data/missing-port test and the
  returned-generic-callable predecessor pair. The consolidated full library
  checkpoint passes all 1,059 tests. The source corpus now contains 49 tests.
  Measured unchanged-call successor work would save only 5,613 units through
  five focused checks, so no call-choice cache was added.
- Structural profiling identifies repeated reachability pruning as the larger
  cost. Its `value::close` bucket was invalid because a loop-line breakpoint
  double-counted work; it is excluded from the decision. A normalized singleton
  stack pop can make only the old root unreachable, provided it has no live
  capture. The narrow scan retains self-cycles and live incoming references;
  multiple-edge or live-capture roots use full pruning. Bounded review and
  differential graph/capture tests support that correction.
- The parent passes 30 capture tests and 48 of 49 source tests after the pop
  correction. Both recursive-owner pairs pass; the completed-factory inherited
  control alone exhausts in its seventh check. That check starts at 308,995
  charged type-work units. The next bounded measurement replaces the second
  binary edge bound with a charged contiguous equal-address scan; no map,
  candidate omission or higher work limit is introduced.
- The edge-range differential and singleton-pop exact tests pass independently.
  Tiny pop cases retain semantic comparisons; a wider chain owns the strict
  work-saving claim. One-bound lookup reduced work further but did not close
  the factory case. A transient address-range index inside full pruning then
  brings the parent's complete source gate to 49 of 49, plus its small-stack
  child. Every entry and dependency check remains present, and limits are
  unchanged. The index is local scratch state, not retained analysis metadata.
  Fresh internal index/full-library gates and the remaining publication,
  linking, independent-Core and final-review obligations are still required.
- The parent independently passes the fresh 1,062-test library and expanded
  51-test source corpus, including the unchanged small-stack child. The source
  publication guard is removed after successful dependency/control proof;
  positive module tests now require actual checking success. Ordinary exported
  resource functions and implementation-only resource methods both publish,
  import and link, reaching the separate final Core execution guard.
- Implementation-only publication exposed a private method-catalog assumption:
  dependency order differs from identity order across builtin/source namespaces.
  Charged canonical ordering repairs that path without changing identities or
  duplicate rejection. Full linked-owner tampering and exact-boundary tests
  remain in progress; the runtime guard remains closed.
- A bounded same-site dispatch investigation found no defect. Fresh-identity
  recursive forwarding rejects as polymorphic recursion; legal monomorphic
  forwarding rejects unsafe discard and admits the matching resume control
  through source checking. No additional identity mechanism is justified.
- The fresh parent build passes all 1,064 library tests and 11 Effect module
  tests. Real linked-resource tests cover ordinary and implementation-only
  owners, full constraint/type exact boundaries, one-short failures and two
  fresh retries, surplus identities and detached/mismatched acquisitions.
  The catalog test also rejects duplicate method identities after ordering.
  Bounded semantic review found no ordering defect. The existing public Core
  and module tests reproduced their obsolete source-guard expectations. After
  migration, the parent passes all 63 resource Core/module/typing tests and the
  unchanged small-stack child. Direct acquisition now requires real checking
  success; CLI execution still rejects at the internal runtime guard.
- A genuinely published and linked resource program reaches the final execution
  guard before and after both Core transforms. The parent independently passes
  its same-typed constant-to-capturing-closure tamper test: both rebuilt graphs
  reject the changed result as resource escape. Request-payload tampering,
  exact real-Core work, source-publication atomicity and final reviews remain
  in progress. Runtime cells have not started.
- The request-payload variant exposes a predecessor Core registry-order defect
  before dependency checking. A resource-free program importing the cell API
  and declaring an ordinary effect also rejects as `core.validation.registry`
  on this revision and the Step 3 baseline; removing only that import returns
  `42` on both. Debugger evidence identifies a numeric cross-module ordering
  predicate, whereas combined facts retain dependency order and builtin/source
  namespaces have a different total order. The bounded correction must preserve
  exact per-module declaration order, duplicate rejection, indexed lookup,
  source authentication and charged work. No effect identity or handler rule
  changes; the unchanged payload witness remains required.
- The parent independently passes the correction's 1,067-test library. Core
  now checks charged, fallibly reserved per-module effect ordinals, preserving
  duplicate/gap/reversal rejection and exact indexed/source relationships.
  Bounded semantic review supports that boundary without producer reordering.
  The real linked result and request-payload fixtures pass their exact work
  boundaries and both transforms; same-typed dependent substitutions reject
  as resource escape. The parent also passes late source-publication failure:
  a one-short final reservation leaves earlier pending evidence unselected,
  while both exact fresh retries publish successfully. Full focused gates,
  self-review and final Step 4 reviews are next; runtime remains closed.
- The frozen Step 4 review checkpoint passes all 1,269 focused tests plus the
  unchanged small-stack child. All 32 architecture checks pass; the owner scan
  took 289 seconds. Strict Clippy, formatting and documentation checks pass.
- Fresh semantic review found one unjustified rejection: strict value equations
  retain results from continuations skipped by safe inside-owner discard.
  The parent reproduces match, call and tuple cases, plus the same cause in a
  primitive operand and nested acquisition initializer. The equivalent preceding
  binding passes. The writer is correcting child readiness using existing
  reader wakeups; metadata-only merges and latent closure captures are not
  strict children. Retain positive discard and negative resume controls, then
  re-review before Rust/resource review. Step 4 remains unaccepted.
- The readiness correction passes the parent's five-shape source/domain tests,
  including resumed-escape negatives and exact late-value retries. All six
  independent CLI probes, including the preceding-binding control, now reach
  the intended final execution guard. The fresh library passes 1,068 tests;
  resource Core/module/typing gates pass 1/11/53 plus the small-stack child.
  Semantic re-review closes the finding without another concrete blocker.
  Source is frozen for a fresh high-reasoning Rust/resource review while the
  corrected full focused gate runs. Strict Clippy and formatting pass.
- The corrected full gate passes 1,271 tests plus the small-stack child, with
  all 32 architecture checks. Rust/resource review identifies two P2 findings:
  several new value/control staging buffers reserve or copy their width before
  the owning work charge, and a copied implementation-method body type crosses
  a fallible parameter clone without iterative ownership. The reviewer proves
  the failure paths but does not claim an observed stack overflow. The writer
  is adding preflight and deep-failure evidence before bounded corrections;
  no limit increase, omitted proof query or semantic redesign is authorized.
- The staging correction now charges buffer width before all seven reported
  reserves or copies. The parent independently passes 57 wide tests, including
  six new owning-boundary tests with insufficient-prefix and exact fresh retries.
  The method-type regression reproduces a stack overflow in an isolated 64 KiB
  child before the correction. The actual method-root path now uses the existing
  iterative type owner through its fallible parameter copy; the unchanged deep
  failure/retry test passes independently. Full corrected gates and Rust/resource
  re-review remain required before the Step 4 commit. Runtime is not started.
- Step 4 is accepted: the corrected full gate passes 1,278 tests plus the
  unchanged small-stack child, including all 32 architecture checks. Both
  independent reviews are closed; Rust/resource re-review independently passes
  15 relevant tests. Strict Clippy, formatting, diff checks, Markdown lint and
  all five local links pass. Retain this static-proof increment in an unsigned
  local commit, then begin runtime cell ownership and release. All seven
  prepared runtime probes still reach the final execution guard.
- Step 4 is retained in unsigned commit `a841d46`; the worktree was clean after
  the commit. A fresh high-reasoning sole product writer is starting Step 5's
  runtime cells, activation matching, capture retention and release. The parent
  retains documentation, Git and independent verification ownership. Main and
  integration are unchanged; nothing was pushed or tagged.
- Step 5 begins with four durable execution tests failing at the expected final
  guard. Independent probes for metadata-only same-site activation and a copied
  closure called after release also reach that guard. A further interaction
  probe exposes a static rejection: an imported accessor works directly and
  under a nested cell, but invoking it through a row-polymorphic tuple helper
  reports resource escape. Debugger evidence places the failure in request-
  payload checking of the builtin read, not result-type escape. A read-only
  diagnosis proceeds alongside runtime implementation; no static proof is
  weakened and any product correction will retain one writer.
- Initial runtime implementation passes its first four durable tests. The
  parent independently executes 11 probes, all returning `42`: the seven
  prepared cases plus direct/nested imported accessors, metadata-only same-site
  activation and a copied closure invoked after release. Runtime frames own
  payloads; handles retain activation keys. The final execution guard has been
  removed in the uncommitted runtime increment. Capacity, failure disposal,
  complete interactions and independent reviews remain open, as does the
  row-polymorphic relay rejection.
- Debugger inspection confirms the relay defect: call-context matching receives
  an actual callback with only row tail `E`, while its current context holds the
  concrete cell effect. Ordinary type substitution does not expand that tail,
  so the accessor's identity parameter remains unspecialized. The resulting
  builtin read is treated as potentially crossing its own scope. Correct the
  missing row-variable substitution in the existing finite context, not handler
  selection based on handle ownership. Distinct row variables must remain
  separate; one enclosing row cannot stand in for every tail. Runtime work will
  freeze before the previous writer receives this bounded product correction.
- Runtime reaches a tested pause: 1,217 focused tests plus the unchanged
  small-stack child pass (library 1,082; Effect runtime 26; polymorphism 43;
  resource runtime 13; resource typing 53). The runtime writer has frozen and
  relinquished ownership; the previous static writer now owns the bounded
  row-substitution correction. The local equivalent also reproduces the
  rejection. Runtime capacity/instantiation evidence, remaining lint/architecture
  checks and independent reviews remain after that correction.
- During the static handoff, the parent independently passes six runtime
  ownership tests: live capacity/reuse, atomic context failure, pure locality,
  deep completion/disposal in a fresh test process, retained capture and
  rejected discard, and wrong-key/operation rejection before mutation. A full
  source program with 24 nested acquisitions also executes and returns `42`.
  The unchanged row-relay regression is retained as a durable failing test
  before its correction; these runtime passes do not close that static defect.
- The first row correction passes its owning exact/retry unit and the six
  local/imported source variants. The parent independently executes the four
  original failing CLI fixtures to `42`, plus separate `E`/`F` callbacks and a
  helper that handles one known effect while forwarding the remaining row.
  Hidden outward payload and skipped outer-resume negatives still reject;
  copied/live-outer payload and inside-scope discard controls remain admitted.
  Canonical empty-row, ambiguity/lacks, finite-context and transformed-Core
  checks remain before this correction returns to runtime verification.
- Empty-row normalization now passes its unchanged regression. Lacks,
  conflicting row equations, finite argument retention and the imported relay
  through both independently validated, executed Core rebuilds also pass,
  including parent checks. The next independent library run passes 1,087 tests
  and fails only a new regression for uncharged nullary row-universe scanning.
  The static writer is correcting that owning work charge before final gates
  and the runtime handoff. Step 5 remains open; no default limit was raised.
- The scan regression is now green; the parent independently passes all 1,088
  library tests. Effect predecessor suites, resource typing (56 plus the
  small-stack child), resource runtime (13) and strict Clippy pass. The broad
  command exposes an obsolete admission test: it expects an execution guard
  but receives `42`. Migrating that test and removing the unused guard reason
  belong to the returning runtime writer. Documentation lint, diff checks and
  the five local task/plan links pass. Reviews and local integration remain open.
- Static self-review corrects one matching omission in the initial type-subtree
  scan: nullary known/lacks instances now charge before traversal. Its isolated
  regression fails before and passes after the correction. The final gate
  passes 1,089 library tests and 56 typing tests plus the child; the parent
  independently reruns all 1,089 library tests successfully. Runtime evidence
  and full independent reviews remain open.

- Runtime is frozen for independent review. Its final gates pass 1,093 library
  tests, 298 integration tests plus two child checks, 75 specification examples
  and strict Clippy/fmt/diff. Architecture's 31 passing full-scan tests plus the
  corrected missing-field inventory test cover all 32 cases; the complete
  closure gate remains required. Parent verification independently passes all
  1,093 library tests and 14 runtime tests plus the child process.
- The parent drafted all eight proposal-named specification/tool areas and
  the resource-scope evidence report. The documented CLI example now passes
  its exact source/output test. Markdown lint and 26 existing local spec/tool
  links pass. A fresh high-reasoning semantic review covers Steps 5 and 6's
  complete contract; a medium-reasoning documentation audit runs independently.
  No Step 5 commit, final acceptance or local integration is claimed yet.
- Documentation re-review approves all eight specification/tool areas after
  adding resource handles to the runtime inventory, the resource carrier to
  the exhaustive Core list, and the no-nearer-cell premise to source-handler
  selection. The audit resolves 188 local links including anchors. Semantic
  review independently passes focused gates and opaque transport probes;
  the parent repeats both opaque acceptance cases (`42`) and the escaping
  opaque closure rejection (`type.resource-escape`). Retaining that exact
  regression set remains a review action, not a new semantic decision.
- All five opaque/evidence witnesses are retained unchanged as real-driver
  tests. The focused five and full library (1,093)/typing (61 plus child) gates
  pass; semantic re-review approves and closes its only evidence gap. No
  semantic/authority findings remain. A fresh high-reasoning Rust/resource
  reviewer now owns read-only verification; product writers remain frozen.
- Final Rust/resource review finds one P2 work-accounting omission, with no
  runtime ownership finding. When a callback's actual row is pure or has an
  unresolved tail, formal known effects are visited before either `continue`
  branch charges the scan. An isolated copied-source witness measures the
  same work at widths 1 and 4,096 (7 for pure, 12 for open). The runtime writer
  now owns this bounded regression/correction; review and full verification
  remain open until it passes and is re-reviewed.
- The formal-row scan correction passes its unchanged RED-to-GREEN regression,
  all 22 control tests, library (1,094), typing (61 plus child), runtime (14 plus
  child), strict Clippy/fmt/diff. The parent independently passes all 1,094
  library tests. Rust/resource re-review closes the P2 and reports no remaining
  finding. The subsequent full `CARGO_INCREMENTAL=0 cargo xtask verify` passes
  build, strict Clippy, library, CLI and all 32 architecture tests, but fails
  unchanged synthesized-wrapper stack and 10,000-member cycle work tests.
- The parent runs every unreached integration suite with `--no-fail-fast`.
  Three more predecessor failures remain: nested supplied methods and deep
  recursive calls exhaust type work; an exported closure factory fails import
  admission because its summary references missing nominal metadata. Read-only
  diagnosis traces the wrapper to enlarged elaboration frames and the cycle
  to newly unconditional Pure capture-summary publication. The sole writer
  first extracts resource phases from the large dispatcher; independent review
  checks whether a private Pure module has no portable-summary consumers.
  Tests and production limits remain unchanged. Full verification, checkpoint
  retention and transition cleanup remain open.
- The stack-only correction moves four resource/perform phases into helpers,
  preserving task order, charges and boxed ownership. The unchanged fresh
  256 KiB wrapper test passes independently; library (1,094), typing (61),
  runtime (14), child tests and strict Clippy/fmt/diff pass. Semantic and
  Rust/resource reviews approve this bounded extraction.
- Independent traces put all three work failures in unnecessary Pure portable
  summary construction. Semantic review approves skipping construction only
  when no local public term or implementation method consumes a summary;
  all Effect proofs and all roots of an enabled graph remain required.
  The factory failure is separate: its graph-internal lexical nominal must not
  enter ordinary imported nominal facts. Preserve the complete capture graph
  and inventory its nonlexical nominal references separately; ordinary scheme
  admission, graph authentication and lexical-escape checks remain strict.
  Both corrections require implementation evidence and re-review.
- The empty-demand Pure publication guard passes both independent reviews and
  three new owning tests: private defaults, public/helper/method retention,
  and exact/one-short/fresh-retry scan accounting with identity tampering.
  The parent repeats those tests and the unchanged wrapper. The complete writer
  gate passes library (1,097), data (32), interface resources (6), recursion (10),
  resource runtime (14), typing (61), child tests and strict Clippy/fmt/diff.
  All four stack/work predecessors now pass unchanged; the 10,000-member cycle
  completes in 107.03 seconds. The sole writer now corrects the separate factory
  metadata boundary, retaining type-embedded effects as well as external
  nonlexical nominals. Full verification and integration remain open.
- The capture-only metadata correction passes both independent reviews.
  The parent independently repeats the unchanged factory, generic direct/
  facade/diamond and implementation factories, resource-escape control and both
  deep/exact/retry inventory units. The writer's final gate passes library
  (1,099), scoped evidence interactions (53), local newtypes (20), interface
  validation (2), resource runtime (14), typing (61), children and strict
  Clippy/fmt/diff. All five predecessor regressions are corrected. Product
  writers are frozen; the parent runs a fresh complete
  `CARGO_INCREMENTAL=0 cargo xtask verify` before checkpoint retention.
- That complete run passes library (1,099) and 31 architecture checks; the
  remaining architecture check reports exactly two stale source-location keys.
  The borrowed resolver traversal moved from `retain_type_nominals` into
  `retain_type_nominals_with`. Independent review confirms the same two fields
  and unchanged ownership classifications. Update those inventory locations,
  retain the bidirectional check and rerun the complete gate.
- Both inventory locations are corrected with their classifications unchanged.
  The existing bidirectional test passes for the writer and independently for
  the parent; formatting and diff checks pass. The documentation audit approves
  all eight areas and 188 links, including anchors. The final corrected tree
  is frozen for a fresh complete verification run before local closure.
- The final complete gate exits successfully: 2,365 top-level tests across 67
  binaries, two reported resource child runs, all 32 architecture checks,
  formatting, metadata, build, strict Clippy and warning-denied rustdoc. Parent
  confirms the verified source/test/specification surface stayed unchanged.
  Implementation and complete interaction/review steps close. Retain this
  checkpoint, then remove transition artifacts and perform the approved
  unsigned local integration and clean-worktree lifecycle.

## Verification

Use the proposal's positive, negative, abstraction, repeated-acquisition,
tamper, transform, exact-boundary/retry, deep teardown and locality corpus.
Run focused gates after each increment and `cargo xtask verify` at closure.
Verify changed documentation, links and artifact authority manually.
Only close CP/task/plan after the full implementation and evidence are retained.

## Discoveries

At the baseline, generic effect type applications erased instantiation before
runtime request selection. A generic `E<T>` helper under `E<Int>` failed with
`runtime.invalid-control-state`; monomorphic and internally handled controls
passed. Returned requesting closures failed similarly. CP-0017 explicitly corrects
this prerequisite and the corresponding blanket type-erasure wording.

Source-generated type abstractions contain inert values, transparent type
operations or authenticated method adapters, but Effect Core previously
admitted arbitrary bodies. Delaying those
arbitrary bodies could delay effects. Step 1 therefore independently enforces
the actual lowered forms before retaining lexical abstractions. This preserves
source order and avoids a general runtime aggregate-specialization mechanism;
Pure Core and source generalization are unchanged.

The method-adapter corpus found another prerequisite omission: linked evidence
comparison handles pure function signatures but omits the effectful-function
case when substituting interface parameters. Even a non-generic implementation
with a generic effectful method is checked, then rejected as
`evidence.validation.unknown-identity`. Step 1 includes the narrow structural
comparison repair, with charged substitution and exact-row negative controls;
this does not change interface selection or authorization.

After that comparison repair, the same generic adapter reached Core and
exposed incomplete method-parameter renaming. The function type used its fresh
generated binder, but the body row still used the resolved method binder.
The owning Core rewrite seam handled ordinary types and type-application row
arguments but skipped expression rows and Effect operation/pattern metadata.
Step 1 corrects that seam with the existing charged callbacks and tests the
complete relationship; independent validation is not relaxed.

Independent semantic review reproduced valid ordinary and generic-method
forwarding of a pure lambda through an open-row helper. Zonking that row to
empty normalizes its function wrapper to a pure function, but two existing
callbacks assumed an effectful function and panicked. Step 1 handles both
canonical forms and retains the empty/nonempty controls. The reviewer found no
additional semantic defect in lexical runtime contexts or the abstraction gate.

The resource reviewer measured width-dependent allocation under constant
admitted work: a nonempty lexical context substituting a function type with
one wide effect instance spent four units before exhaustion, while staging
grew with argument width. The shared substitution helper flattened known/lacks
arguments before charging their visits. Step 1 must preflight that staging or
stream it through bounded state; both known and lacks rows require controls.

Ordinary closure environments retain unused preceding bindings, while ordinary
heap cells persist into observation. Resource payload ownership must therefore
stay with the acquired scope; non-owning access handles must not extend it.
Capture analysis currently has callable targets and clause owners only. New
stored dependencies and resource-owner obligations must be inferred even when
resource-bearing code contains no discard.

## Deviations

No scope expansion is authorized. The original 16/100 milestone forecast is a
relative weight, not a spent-work ledger or a new numeric budget. Do not invent
work-unit totals or borrow hooks, cleanup, FFI or a general ownership system.
