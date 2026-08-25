# TASK-0014: Finish Modular Ash

- ID: `TASK-0014`
- Status: active
- Related: [DN-0020: Ash Dialect Milestones](../design/DN-0020-ash-dialect-milestones.md), [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), [AD-0004: Small-Step Semantic Method](../decisions/AD-0004-small-step-semantic-method.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), and [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md)

> This task organizes work. It does not define Ash semantics. A semantic
> discrepancy returns to proposal or design work rather than being resolved
> here.

## Dependencies

The current specification defines Modular Ash. DN-0020 records the comparison
and closure planning criteria, and DN-0025 records descendant pressure and
exclusions for later library and package milestones. The user's explicit request
authorizes this task to finish the Modular Ash milestone. The temporary
[execution plan](../plans/2026-08-25-finish-modular-ash.md) owns the ordered
work and leaves the current tree when this task finishes.

## Work

- Establish paired evidence for one retained intrinsic and one operation
  expressed through an explicit library interface.
- Compare their admission, typing, diagnostics, Core, evaluation, maintenance
  sites, and resource and ownership consequences.
- Simplify or reconcile only machinery or evidence proven unused or stale; do
  not change admitted behavior, diagnostic ownership, Core validity or shape
  obligations, or evaluation. A finding that would change any of those returns
  to new authorization.
- Retain core-versus-library and Modular Ash closure reports, then obtain fresh
  review and full verification.
- Remove this task and its temporary plan after the retained closure checkpoint,
  make unsigned commits, create an annotated unsigned `modular-ash` tag, and
  leave the branch unmerged.

The work excludes new language semantics; `lib-ash` and `pack-ash` mechanisms;
prelude or implicit imports; an operator rewrite; module signatures, reexports,
packages, caches, or object linking; and interface extensions.

## Progress

The paired integer-equality witness and complete core-versus-library comparison
are retained. A focused architecture guard proved and now enforces two
post-authentication lifetime boundaries: the linked-interface registry remains
local to validation, and the driver releases the validated interface program
after Core synthesis finish and before independent Core validation. The Modular
Ash closure report and informative design-note reconciliation are complete.
Final independent reviews, lifecycle cleanup, root verification after cleanup,
the closure commit, and the annotated tag remain.

## Verification

- Establish that the focused target or case for each new audit witness was
  absent, then run the retained witness against current behavior.
- Before stale-or-unused reconciliation, establish an architecture or invariant
  witness that detects the unwanted retained state. Recheck that the cleanup
  preserves admitted behavior, diagnostic ownership, Core validity and shape
  obligations, and evaluation.
- For each increment, perform focused checks, then an independent specification
  review followed by an independent code-quality review.
- Before closure, review the retained reports and run the full required
  verification suite.
- Correct review findings only when they are within this task's bounded audit
  and proven stale-or-unused reconciliation scope. Return semantic or broader
  findings to design, proposal, or new authorization.
- After lifecycle cleanup, perform an independent specification-and-authority
  review followed by a code-quality review. Re-review after each in-scope
  correction, then repeat final verification before the closure commit and tag.
- Check changed Markdown with the available Markdown linter, inspect every
  changed relative link manually, and run `git diff --check`.
- Confirm the closure commit and annotated `modular-ash` tag are unsigned and
  that the branch remains unmerged.

The fresh pre-cleanup `cargo xtask verify` closure checkpoint passed formatting,
metadata, build, denied-warning Clippy, every test, and denied-warning rustdoc.
Its exact inventory is 298 library tests, 10 binary tests, 625 integration
tests, and one `xtask` test: 934 tests with no failures. The closure-document
increment also checks Markdown lint, every changed relative link, authority
boundaries, stable maintenance searches, and `git diff --check`. Root
verification and both independent reviews repeat after lifecycle cleanup.

## Discoveries

- Interface-era linking and evidence validation consume
  `ResolvedModuleProgram.entry` and each group module identity for entry-closure
  and ownership authentication. The passive-module report's earlier no-reader
  observation was historical, so those fields remain.
- An explicit post-synthesis drop closes the long checked-program lifetime
  without introducing a separate consuming synthesis payload. A returned
  structural value owns its heap through `ObservedValue`; the separate
  observation heap remains necessary when a returned closure captures an
  environment containing raw heap locations.
- The paired equality audit retains integer `==` and `Primitive::Equal` while
  showing that an explicit `Equal<Int>` source-library capability needs no new
  Core or evaluator form. The paths intentionally keep different admission,
  typing, diagnostic, Core, and trace behavior; no prelude or package is
  implied.
- Associated types, specialization, library re-exports, packages, caches, and
  separate linking are later design pressure rather than missing Modular Ash
  closure work.

## Deviations

None. Any semantic gap or discrepancy returns to proposal or design work
instead of being resolved by this task.
