# TASK-0014: Finish Modular Ash

- ID: `TASK-0014`
- Status: active
- Related: [DN-0020: Ash Dialect Milestones](../design/DN-0020-ash-dialect-milestones.md), [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), [AD-0004: Small-Step Semantic Method](../decisions/AD-0004-small-step-semantic-method.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), and [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md)

> This task organizes work. It does not define Ash semantics. A semantic
> discrepancy returns to proposal or design work rather than being resolved
> here.

## Dependencies

The current specification defines Modular Ash. DN-0020 defines the comparison
and closure criteria, and DN-0025 records descendant pressure and exclusions
for later library and package milestones. The user's explicit request
authorizes this task to finish the Modular Ash milestone. The temporary
[execution plan](../plans/2026-08-25-finish-modular-ash.md) owns the ordered
work and leaves the current tree when this task finishes.

## Work

- Establish paired evidence for one retained intrinsic and one operation
  expressed through an explicit library interface.
- Compare their admission, typing, diagnostics, Core, evaluation, maintenance
  sites, and resource and ownership consequences.
- Simplify or reconcile only machinery or evidence proven unused or stale; do
  not infer a semantic change from that cleanup.
- Retain core-versus-library and Modular Ash closure reports, then obtain fresh
  review and full verification.
- Remove this task and its temporary plan after the retained closure checkpoint,
  make unsigned commits, create an annotated unsigned `modular-ash` tag, and
  leave the branch unmerged.

The work excludes new language semantics; `lib-ash` and `pack-ash` mechanisms;
prelude or implicit imports; an operator rewrite; module signatures, reexports,
packages, caches, or object linking; and interface extensions.

## Progress

Authorization checkpoint created. The audit, witnesses, retained reports,
review, verification, cleanup, commits, and tag remain.

## Verification

- Establish that the focused target or case for each new audit witness was
  absent, then run the retained witness against current behavior. Use RED only
  before a cleanup that changes behavior.
- For each increment, perform focused checks, then an independent specification
  review followed by an independent code-quality review.
- Before closure, review the retained reports and run the full required
  verification suite.
- Correct review findings only when they are within this task's bounded audit
  and proven stale-or-unused reconciliation scope. Return semantic or broader
  findings to design, proposal, or new authorization.
- Check changed Markdown with the available Markdown linter, inspect every
  changed relative link manually, and run `git diff --check`.
- Confirm the closure commit and annotated `modular-ash` tag are unsigned and
  that the branch remains unmerged.

## Discoveries

None yet.

## Deviations

None. Any semantic gap or discrepancy returns to proposal or design work
instead of being resolved by this task.
