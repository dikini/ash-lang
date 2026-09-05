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
