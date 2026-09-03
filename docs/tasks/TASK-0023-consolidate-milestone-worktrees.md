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
- The Task 1 baseline recorded these protected refs:

  ```text
  main                                      7195500b7a165f8191efa1485e1ca6f4114180fb
  integration/effect-ash-foundations        c9bc0faf77ea4aa1310ed5a8f207ef2ff83274f9
  feature/cp0014-local-newtype              b5f6c128200aa53e935613b9e2215f5266cf99ee
  planning/effect-ash-program               cddb712f24ac7c57da48015227105b57da5b20a2
  planning/effect-kernel-proposal           e5f7340dd5e6f88ec883bfb41daf5386ffb27100
  ```

- Ten worktrees were registered: the main checkout, two excluded detached
  worktrees, and seven scoped worktrees under `.worktree/`. All seven scoped
  worktrees were clean. The three required ancestry checks succeeded.
- `cargo xtask verify` exited zero after format, metadata, build, Clippy, test,
  and documentation checks. Its test phase discovered and passed 1,912 tests.
  Markdown lint with MD013 disabled and `git diff --check` also exited zero.
- Verification populated ignored build output and increased `.worktree/` from
  49 GB to 52 GB. An ignored-file audit of all six removal candidates found
  only `target/` in each checkout; no ignored source or evidence artifact needs
  retention.
- The baseline tag snapshot is:

  ```text
  refs/tags/lib-ash     3173abcf54ec512dcf1b1bf10713faf312917f5e
  refs/tags/mini-ash    819a9b249a19b2399f23ea1ea3a7251e1ed1701a
  refs/tags/modular-ash d6cce6e7c4a7751b1b7306aca4977ddb1fccfb16
  ```

- The baseline remote-ref snapshot is:

  ```text
  refs/remotes/origin/HEAD 7195500b7a165f8191efa1485e1ca6f4114180fb
  refs/remotes/origin/main 7195500b7a165f8191efa1485e1ca6f4114180fb
  ```

- Task 1 performed no cleanup. It changed no worktree registration, feature
  ref, planning ref, tag, remote ref, source file, specification file, or
  product test.
- Task 2 removed the CP-0010, CP-0012, and CP-0013 worktrees cleanly with
  `git worktree remove` and no `--force`. Their feature refs were deleted with
  `git branch -d` after the required ancestry checks. The exact former tips
  remain reachable and readable through `main` or the integration branch:

  ```text
  feature/cp0010-method-local-type-parameters dbe4299c9a0dbee72a94e3f7ba5a85663b2653fd
  feature/cp0012-module-newtype                e581296d27966d1f49d74ce7b7f140b2885100ba
  feature/cp0013-effect-kernel                 378a39cf17ef16c8917051c07f6be5c54e0f1baa
  ```

- Task 2 reduced `.worktree/` disk use from 52 GB to 33 GB.
- Task 3 removed both planning worktrees cleanly with `git worktree remove`
  and no `--force`. It moved the exact planning tips to these archive refs:

  ```text
  archive/planning/effect-ash-program     cddb712f24ac7c57da48015227105b57da5b20a2
  archive/planning/effect-kernel-proposal e5f7340dd5e6f88ec883bfb41daf5386ffb27100
  ```

- The old `planning/effect-ash-program` and
  `planning/effect-kernel-proposal` refs are absent. Task 3 reduced
  `.worktree/` disk use from 33 GB to 25 GB.
- Before Task 4, the protected active refs resolve exactly as follows:

  ```text
  main                               7195500b7a165f8191efa1485e1ca6f4114180fb
  feature/cp0014-local-newtype       b5f6c128200aa53e935613b9e2215f5266cf99ee
  integration/effect-ash-foundations d56bb80947f0b065fcb3cac00e8e0ec3a01dca6d
  ```

- The tag and remote-ref snapshots still match the exact Task 1 baselines.
  Five worktrees remain registered and clean: the main checkout, the two
  excluded detached documentation worktrees, CP-0014, and integration. Only
  CP-0014 and integration remain under `.worktree/`.
- Tasks 2 and 3 followed the plan without deviations. They changed no remote
  ref, tag, source file, specification file, or product test.

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
- `git for-each-ref` output for tags and remote refs exactly matches the
  baseline snapshots above. No source file, specification file, or product
  test changes.

## Discoveries

None.

## Deviations

None.
