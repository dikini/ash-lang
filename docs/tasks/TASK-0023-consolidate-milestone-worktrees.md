# TASK-0023: Consolidate Milestone Worktrees

- ID: `TASK-0023`
- Status: active
- Related: [AD-0011: Milestone Worktree Lifecycle](../decisions/AD-0011-milestone-worktree-lifecycle.md), [execution plan](../plans/2026-09-03-consolidate-milestone-worktrees.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

AD-0011 accepts one integration branch and at most one checked-out active
product checkpoint as the Effects Ash continuation structure. The user
separately approved worktree removal and local branch cleanup while retaining
the milestone gate: do not merge Effects Ash into `main`.

All seven worktrees under `.worktree/` must remain clean until their planned
removal. Preserve the exact planning tips by moving their refs to
`archive/planning/`. Delete a completed feature ref only after proving that its
tip is an ancestor of `main` or `integration/effect-ash-foundations`.

Do not change, merge, remove, or rename `feature/cp0014-local-newtype`. Do not
touch the detached worktrees under `.config/superpowers`, any remote ref, or
any tag. Do not push.

## Work

- Record all affected object IDs, worktree cleanliness, ancestry, and disk use.
- Remove the three completed feature worktrees and their redundant local
  feature refs.
- Remove the two superseded planning worktrees and move their exact refs under
  `archive/planning/`.
- Remove the idle integration worktree while retaining its branch.
- Retain only `.worktree/cp0014-local-newtype` as the active product checkout.
- Verify that `main`, integration, CP-0014, and both archived planning tips
  still resolve to the intended commits.
- Record the result, remove this task and its plan, and leave the accepted
  lifecycle decision on the integration branch.

## Progress

- AD-0011 records the approved lifecycle and intentional exclusions.
- No worktree or branch ref has changed.

## Verification

- `git status --short` is empty in each worktree before removal.
- `git merge-base --is-ancestor` succeeds for every feature branch deleted.
- Each archive ref resolves to the planning tip recorded before its rename.
- `git worktree list --porcelain` shows no removed path and retains the main,
  CP-0014, and external detached worktrees.
- `find .worktree -mindepth 1 -maxdepth 1 -type d` reports only the CP-0014
  worktree.
- `main` remains at its original object ID, CP-0014 remains at its original
  object ID, and the integration ref retains the cleanup documentation.
- `git diff --name-only fa26025..integration/effect-ash-foundations` contains
  only the accepted lifecycle decision and its index after transition cleanup.
- No remote ref, tag, source file, specification file, or product test changes.

## Discoveries

None.

## Deviations

None.
