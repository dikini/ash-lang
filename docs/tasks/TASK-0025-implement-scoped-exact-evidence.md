# TASK-0025: Implement Scoped Exact Evidence

- ID: `TASK-0025`
- Status: active
- Related: [CP-0015](../proposals/CP-0015-scoped-exact-evidence.md),
  [execution plan](../plans/2026-09-05-scoped-exact-evidence.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

CP-0015 is accepted at `2f657d8` under the user's explicit request to implement
the bounded slice autonomously. The product baseline is verified integration
tip `90f517d`. The active branch is `codex/scoped-exact-evidence` in the ignored
`.worktree/scoped-exact-evidence` checkout. Main-checkout diagnostics and
migration-planning changes are unrelated and must remain untouched.

The original forecast is seven relative milestone units, not a token/time
budget. The user sets no new numerical work cap. Keep one product writer and
use independent read-only subagents: high for implementation and semantic or
resource risk, medium for mechanical mapping and documentation. High is the
ceiling. No generic evidence framework, new solver, or prototype is authorized.

## Work

1. Carry the smallest pure-relation direct/forwarding pair through syntax,
   resolution, selection, linked authentication, ordinary Core, and execution.
2. Complete CP-0015's selection, improvement, method, and closure interactions.
3. Close tamper, resource, small-stack, and predecessor coverage with independent
   semantic and Rust/resource reviews.
4. Update normative specification and executable examples, run the full gate,
   retain evidence, close transition artifacts, and reconcile the completed
   checkpoint with the local milestone integration branch under AD-0011.

This does not authorize a merge into `main`, push, or tag. Use unsigned commits.
Return semantic gaps to CP-0015; a scope expansion requires user direction.

## Progress

- Baseline `CARGO_INCREMENTAL=0 cargo xtask verify` passed on 2026-09-05:
  formatting, metadata, build, Clippy, 1,968 tests across 59 binaries, and
  rustdoc with warnings denied. The ignored baseline log is
  `target/scoped-evidence-baseline.log`.
- Independent high semantic and medium implementation-mapping reviews converged
  the accepted contract. They required explicit method resume barriers,
  complete admission precedence, and inert Core authentication facts.
- The first direct/forwarding pair failed because sequential `with` was absent
  before production edits. Ten independent interaction cases also compiled and
  failed on that missing syntax; their RED log is
  `target/scoped-evidence-interactions-red.log`.
- One high-reasoning agent owns production source and the first-pair test file.
  The root prepares the disjoint `tests/scoped_evidence_interactions.rs` corpus
  and review evidence. The direct/forwarding pair now passes; source and capture
  authentication is still being completed before its reviewed checkpoint.
- The expanded interaction run passed 36 of 39 tests; all six syntax tests
  passed. Two polymorphic-method cases fail Core type validation; a supplied
  effectful method fails during checking. Independent diagnosis identified
  missing local-binding authentication/parameter renaming and source-to-Core
  type projection, respectively. The corrected fixture log is
  `target/scoped-evidence-interactions-corrected.log`.
- Task 3 still owns iterative scheduling for nested supplied method bodies,
  exact resource boundaries, and forged-source tests. Those tests must include
  priority substitution (abstract/current versus lexical, lexical versus
  concrete) and moving an unused checked source outside its nominal scope.
  Passing ordinary selection tests does not establish those validation facts.
- Task 1 semantic review closed with no findings. The root reran the vertical
  pair, syntax, interface-selection, interface, and local-newtype targets:
  all 112 tests passed (`target/scoped-evidence-checkpoint-1.log`). Eight
  focused architecture checks passed after recording the new static carriers;
  runtime inventories and scanner rules remain unchanged.
- Rust/resource review found one uncharged lexical-only plan scan on existing
  programs. A regression observed three inspections where none were needed.
  The correction skips empty-owner paths and charges feature-path inspections;
  two exact-budget/bypass tests and all 200 affected evidence tests pass.
  The reviewer confirmed the correction and closed Task 1 with no outstanding
  Critical or Important findings. Tasks 2 and 3 remain open.
- Task 1 is retained at `f01e8e3`; all-target Clippy also passed before commit.
  Task 2 is active. Its first 42 interaction cases now all pass, including
  polymorphic forwarding, effects, enclosing parameters, and a cross-module
  closure. The importer receives the ordinary factory without its interface or
  implementation facts.
- Task 2 review added four failing witnesses: lexical method-parameter scope
  through preceding/nested evidence, invalid sharing of two methods' rigid
  parameters, and coalescing closed effect instances after substitution. The
  46-case corpus retains these. Corrections must allocate independent contextual
  method rigids and reuse existing canonical row substitution; they add no
  source type namespace, open method rows, or solver.
- Task 3's 32-level nested-method fixture overflows a 512 KiB host stack at
  `f01e8e3` (`target/scoped-evidence-nested-stack-red.log`). Its accepted branch
  is observed RED; a wrong-result branch is also prepared for error disposal.
  The test uses unchanged production limits and disables core dumps for the
  isolated failing run.
- All 46 Task 2 interaction cases now pass in an independent root run
  (`target/scoped-evidence-interactions-task2-final.log`). Semantic re-review
  closed the independent-rigid and canonical-row findings. Function-body row
  weakening now uses the existing subset check required by static semantics;
  ordinary type equality and Pure Core restrictions remain unchanged.
- Task 2 quality review found early-error recursive disposal of a temporary
  replacement map and uncharged contextual-owner scans. Both have concrete
  bounded fixes under review. The writer's predecessor run passed 177 tests
  across 12 targets, plus all 200 evidence tests and all-target Clippy.
- The root has prepared specification and example drafts while Task 3 remains
  open. All 74 specification tests passed before the draft review's small
  consistency corrections. The draft review required the new lexical arm in
  the conceptual selection model as well as the selection judgment; the
  manifest now guards both. These drafts are not Task 2 completion or closure.
- Task 2's two Important quality findings are closed. The deep replacement
  test first overflowed a 256 KiB stack at depth 16,384; retaining arguments
  in the existing iterative buffer through fallible checks fixes disposal.
  Two accounting probes observed missing charges and now cover exact success,
  one-short failure, retries, and zero-cost empty catalogs. No new map owner or
  runtime mechanism was added. Final writer verification passed 201 evidence
  tests, both accounting probes, 105 kind-filter tests, all-target check and
  Clippy, formatting, and diff checks. Task 3 remains open.
- Task 2 is retained at `d87203d`. Task 3 first replaces nested supplied-body
  reentry with the existing projector, resolver, and elaborator queues. Staged
  debugger runs located each recursive boundary. The 32-level, 512 KiB
  accepted/error-disposal fixture now passes without raising limits. The
  original local-newtype target, including its 256 KiB cases, also passes.
- A Task 3 semantic review found that failed supplied methods inside handlers
  could lose their original source diagnostic during cleanup. The new test
  observed `Internal(InvalidState)` instead of `type.definition-result`.
  Staging the resume-pop result after the body's original error fixes this
  under the existing poison-on-failure contract; no general unwind mechanism
  is needed. The root corpus now has 48 cases, including a new nested
  polymorphic source-order/method-slot guard. Scheduling quality review and
  the remaining tamper/resource work are still open.
- The exact historical 256 KiB type-depth predecessor in `data_and_adts`
  still overflows after the first queue conversion, despite the 82-case
  focused run passing. This is a required scheduling correction, not a reason
  to raise stack sizes or limits. Review identified large by-value progress
  transfers from the driver as the first frame-size probe.
- Scheduling review is now closed. Restoring the original outer equation
  orchestration puts final Core construction after each body's driver returns;
  supplied methods keep queued continuations using the same prepare/finish
  helpers. A small equation-phase payload keeps the full task enum out of
  helper argument copies. The historical 256 KiB and nested 512 KiB witnesses
  both pass. The writer's final runs passed 388 focused tests, all-target check
  and Clippy, formatting, and diff checks. Both independent reviews have no
  outstanding scheduling findings. Tamper, capture-use authentication, and
  remaining exact resource ledgers are next.
- Scheduling is retained at `bceb688`. Authentication tests then exposed an
  unused source moved before its nominal declaration and concrete evidence
  replacing an identical complete lexical source at root and prerequisite
  positions. The precedence witness now passes while preserving the
  different-dependent prerequisite fallback. Scope and exact capture-use
  authentication remain open. Reordering intact supplied method groups is a
  valid positive control, not a reason to add source-order metadata.
- Scope authentication must inspect every local nominal in the complete
  application, including dependent arguments absent from method types. The
  bounded implementation choice is a scope-only reuse of the existing ordered
  traversal after catalog construction, gated by nonempty lexical owners.
  This avoids changing source-free stage ordering or adding persistent source
  flags. Its exact charges and failure/retry behavior still require evidence.
- The linked header-scope pass now rejects both moved-source witnesses,
  including the dependent nominal absent from method types. The root freshly
  reran all 48 interactions, the 512 KiB nested-body test, and the historical
  256 KiB type-depth predecessor; all passed. The architecture inventory
  observed exactly one new borrowed type-bearing field,
  `LinkedLocalScope::Method`, and passed after its explicit entry was added.
  Core scope, capture-use authentication, and final resource probes remain open.
- The Core dependent-header scope mutation now rejects after extending the
  existing lexical binding scope check to its complete application. Exact
  capture-use testing has an observed failure: retargeting one occurrence in
  `x + x + y` to `y` survives validation because both binders remain captured.
  This requires authenticating each recorded capture use, not only membership.
- The broader architecture run found the scheduling carrier
  `LexicalEvidenceProgress` missing from the separate method/scope manifest.
  Its explicit entry fixes the focused test without changing scanner rules.
  The source-closed type-field manifest was already complete.
- The full architecture run finished with 29 passing tests and two failures.
  Besides the corrected manifest omission, the narrow-owner guard rejects
  `replacement_types.0.drain` in `retain_lexical_owners`. The writer must route
  that transfer through the buffer's owner-aware API while retaining ordered
  transfer and iterative cleanup; do not relax the guard.
- The transfer now uses existing `pop_owned` with reversed parameter traversal
  after checking arity. The root reran the source-reading narrow-owner guard;
  it passes without a new API or exemption. The new abstract/current lexical
  replacement tests also pass with unowned lexical positive controls.
- Per-use capture authentication now makes the exact-binder regression pass.
  The root freshly reran 2 vertical, 48 interaction, and 6 syntax cases, both
  stack regressions, and the source-closed type-field inventory: all 59 passed.
  Missing/retargeted annotation cases, complete authentication review, resource
  accounting, and the full gate remain open.
- Full authentication review found a same-owner capture collision: two
  ordinals could point to one surviving variable while another use changed.
  Mutation 5 reproduced it. A charged transient `(owner, node)` set rejects
  collisions while preserving nested cross-owner sharing; all three capture
  tests and both independent reviews closed that finding.
- Three selector ingress probes now pin source retention at six constraint
  units, owned pending retention at `5 + has_head`, and the conditional cloned
  fixture at `14 + has_head` plus four type-work units. Depths zero, one, and
  256 preserve constant head cost, rollback, retry, and original occurrence
  scope. All 61 selector tests pass; no production charge correction was needed.
- A clean isolated build after restart passes all 74 executable specification
  tests. The previous cache had zero-length compiled metadata, not a source
  failure. Subsequent verification uses `CARGO_INCREMENTAL=0` and the isolated
  target under `target/scoped-evidence-verify.vSnCfz`.
- The broader Core suite passes 116 tests. The linked suite initially passed
  122 and exposed the unused `LexicalEquationBinder` mutation. A second probe
  confirmed that an empty retained equation group was also accepted. The
  unconditional declaration check now charges and validates every group's
  nonempty, binder-consistent equation list; all 123 linked tests pass. The
  depth-16,384/256 KiB cleanup fixture now supplies a valid nonempty group and
  explicitly proves that its failure still follows deep replacement retention.
- Both independent reviewers closed the unused-equation correction. The
  elaborator ledger then exposed missing parameter-copy, determinant-copy,
  and retained-map-capacity charges. Three failing probes now pass, together
  with a public synthesis failure/poisoning control and all 178 elaborator
  tests. Preparation costs eight constraint units in checking and nine in
  synthesis for the one-method `Read<N, Int>` fixture; cleanup charges
  `(M + 1)C` for `M` members and map capacity `C`, before consuming its buffered
  declaration. This bounded ledger change is under independent review; linked
  and capture ledgers, complete-diff review, and the full gate remain open.
- The complete semantic review required independent Core mutations for lexical
  source identities, full applications, method slots/binders, and contextual
  parameter mappings. The root added those tests, then reproduced two distinct
  missing generic-context cases: hoisting an unused `R<N, A>` source outside
  `run<A>` incorrectly passes Core validation when `A` occurs only in the
  header; a valid `with Read<N, A>` inside a generic implementation incorrectly
  fails final Core with `NodeType`. The new 49th interaction and rigid-header
  mutation are observed failing witnesses, not verified completion.
- A fresh architecture run passed 30 of 31 tests, including both type-field
  inventories and the narrow iterative-owner guard. Its remaining failure was
  the missing explicit private-validator allowlist entry for
  `method_evidence_subtree_contains`. The entry now names that existing static
  authentication helper; scanner rules and runtime inventories are unchanged.
  The focused rerun passes.
- The linked ledger correction passes all 128 linked and 49 interface tests.
  It charges method/equation scans and catalog width, reuses the charged block
  shape pass, and preserves the eight-unit source-free predecessor. New probes
  pin lexical node work at 16, owner retention at `30 + 2T`, the header pass at
  50 constraint/three type units, zero header work without sources, and plan
  ingress at `1 + M`. Both independent reviews closed this bounded ledger.
- All three initial contextual-parameter mutations are genuine Core failures:
  empty count, cross-owner ID reuse, and a bijective cross-owner swap are
  accepted. The test now checks every mutation before reporting failures so
  an earlier failure cannot mask another. A same-kind parameter-order mutation
  is also prepared. Separately, capture-walker audit found uncharged pattern
  seed allocation and nested method/equation retention; these remain bounded
  corrections under the existing type-work budget.
- The two-parameter fixture confirms cross-owner duplicate, bijective swap,
  and within-method same-kind order mutations are accepted. The single-parameter
  empty-count witness remains a separate test so incidental rejection in a
  wider method does not remove it. A fresh high-reasoning agent now owns the
  three Core-context repairs; a separate agent prepares only disjoint capture
  ledger tests. The one-product-writer constraint remains in force.
- The generic-implementation interaction and rigid-header hoist regression now
  pass focused runs. A 50th interaction preserves a valid unused header whose
  dependent mentions its enclosing implementation parameter but neither its
  method type nor nominal representation does. Root review required retaining
  the original source-free catalog stage order while supplementing existing
  implementation-owner records only for lexical-header dependencies. That
  adjustment, contextual-parameter authentication, and full re-review remain
  active; these focused results are not a completed checkpoint.
- All five focused Core tests now pass, including the single-parameter count,
  duplicate/swap/order mutations and full nominal/rigid header scope. Core
  authentication checks existing registry provenance and canonical parameter
  order rather than equating source IDs with generated Core IDs. The complete
  Core and linked suites and all 50 interactions are running, and semantic
  re-review is active. Naming the existing `MethodEvidenceLexicalOwner` row in
  the new private validator helper exposed one further explicit allowlist
  omission; its focused RED is retained and the narrow entry is added.
- Final context-fix runs pass 121 Core tests, 129 linked tests, all 50
  interactions, the small-stack predecessor, and all-target checking. Semantic
  review closes the three findings. It also investigated a coordinated rewrite
  of otherwise unobserved source placeholders and diagnostic origins, then
  withdrew that candidate: it preserved freshness, kinds, generated types, and
  actual scope relations. No universal provenance-authentication requirement or
  mechanism is added. The unsupported negative is removed; its investigation
  log remains distinct from required evidence. Bounded quality/resource review
  of the context fixes also closes without findings. Exact helper probes pin
  header dependency detection at seven constraint units and contextual parameter
  authentication at eleven type units. The explicit private-helper allowlist
  rerun passes. The capture ledger is now the sole product-writing task; its
  seven prepared walker probes retain two valid positives and five resource
  failures before correction.

The capture walker's three missing precharges are corrected. Saved final output
confirms 17 focused capture tests, 118 resolved tests, 180 elaborator tests,
192 Core tests, and 50 interactions pass. Capture expectation retention's
existing `C` precharge was inspected; no additional decomposition was added.

Complete-diff review separately found four recursive type-disposal error paths:
lexical selection lowering, scheduling before provenance ownership, finishing
the polymorphic scheme, and cloning a checked scheme before fallible capture
collection. It also found missing new scan charges in resolution, evidence
auditing, kind checking, and Core lexical prerequisites, plus unreserved
replacement-map retention and infallible copied-ID allocation in lexical
preparation. These remain open pending focused corrections and review. No new
runtime mechanism, production limit, or semantic rule is required. All three
subagents reached the account usage limit after the capture writer released
ownership. The root continues local corrections; independent review remains
required before integration.

The root reproduced and corrected four of those findings. Evidence auditing
now precharges group width before its checked equation-count fold; its fixture
costs `2 + G + GE`, preserves pending entries on one-short failure, and succeeds
on fresh exact retry. Kind traversal charges `G` before visiting even empty
groups, in addition to the unchanged header and equation-edge costs. Two
depth-16,384 tests first aborted on a 256 KiB stack: scheduling failed after
cloning a method type but before provenance ownership, and lexical selection
failed during its second clone while retaining the first. Immediate use of
`IterativeTypeOwner` corrects both; lexical result storage also reserves
fallibly under its existing charge. The fresh full library run passes 973 tests
(`target/resource-audit-kind-type-owners-unit-green.log`). Formatting, diff
checks, and Markdown lint pass. A fresh interaction run also passes all 50 cases
(`target/resource-audit-kind-type-owners-interactions.log`). These corrections
await independent review.

The next local correction covers both `finish_lexical_method` disposal sites.
Separate depth-16,384/256 KiB witnesses first abort while disposing a pending
polymorphic scheme or an unpublished checked-scheme field. Both now use the
existing iterative owner through the subsequent fallible work, preserving
checking order and charges. Preparation now reserves copied-ID vectors
fallibly under their previous constraint charges and precharges/reserves
`P + Q` replacement-map slots per method, where `P` counts interface parameters
and `Q` method-local parameters. Its failing probe previously consumed an
argument-clone unit before detecting a one-short replacement-slot budget.
Eleven focused elaborator tests pass after these corrections; the expanded
polymorphic-slot case is included in the pending full library run.

Resolver lookup now precharges the full local interface table and canonical
method table; imported lookup charges only the canonical method table because
its interface lookup is indexed. Registry retention precharges its separate
parameter buffer before reservation. The local exact formula is
`I + M + 2P + 2C`, with `C` the existing parameter-clone cost; imported lookup
omits `I`. The local width/parameter probe passes, and imported cases are added.
Core's concrete lexical-prerequisite arm now charges `L + M` before its owner
and method scans. Its smallest failing witness used eleven units instead of
thirteen. All known code findings have corrections, and the fresh full library
run passes 978 tests (`target/resource-final-known-fixes-unit.log`), including
the imported lookup and polymorphic-slot cases. All-target Clippy passes with
warnings denied (`target/resource-final-known-fixes-clippy.log`); formatting,
diff checks, and Markdown lint pass. All eight affected targets passed in
`target/resource-final-known-fixes-integration.log`: 31 architecture, 32 data/ADT,
six interface-resource, 20 local-newtype, two vertical, 50 interaction, six
syntax, and 74 executable-specification tests (221 total).

The independent whole-diff code/resource review closed with no remaining
Critical or Important findings. Final semantic review found one additional
Core omission: an unused dependent header argument could change from `Int` to
an unapplied type constructor when its matching owner anchor changed with it.
The regression confirms acceptance before correction
(`target/unused-header-kind-red-confirmed.log`). Lexical owners now reuse the
existing complete-application kind checker, with owner/method scan precharges.
The unchanged valid header and exact/one-short/retry checks are retained.
The corrected tree passes all 979 library tests. A separate fresh run passes
the final eleven-unit exact/one-short/retry assertions. Both reviewers closed
the correction and their complete-diff reviews. The requirement audit found no
missing evidence category; admission-order combinations not individually
isolated in tests were checked directly in the stage ordering. The full gate
passed on 2026-09-06 in `target/scoped-evidence-final-verify.log`: formatting,
metadata, build, Clippy, 2,088 tests across 62 binaries, and rustdoc with warnings
denied. Markdown lint, diff checks, and all 194 local file links in the changed
Markdown passed. Specification/report retention, artifact closure, local
integration, and cleanup remain.

## Verification

For each coherent change retain its failing witness, focused passing command,
diff check, and commit. At the full gate run:

```text
CARGO_INCREMENTAL=0 cargo xtask verify
markdownlint --disable MD013 -- docs spec README.md AGENTS.md
git diff --check
git status --short
```

Review relative links, formal notation, semantic authority, every CP evidence
obligation, source failure ownership, exact work formulas, atomic publication,
retry, iterative teardown, Core transforms, runtime erasure, and no source facts
in summaries/imports. Correct all Critical and Important review findings.

## Discoveries

Existing evidence slots and flat selection plans are reusable. Retaining an
optional lexical-chain head per pending occurrence and one parent link per
source preserves deferred inference without copying active-source vectors or
closing inference early. Independent linked validation must derive availability
from the actual ordered source tree, not trust that retained head.

Ordinary nonrecursive Core method bindings and binder scope can represent
lexical methods and captures. A distinct producer in existing authentication
facts does not require a new runtime scope node or evaluator frame.

## Deviations

None. The user's autonomous instruction delegates bounded design and execution
choices, not new language scope. The proposal records those decisions rather
than duplicating them in a separate design document.
