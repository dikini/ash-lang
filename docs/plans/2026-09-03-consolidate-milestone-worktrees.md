# Milestone Worktree Consolidation Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Reduce the local Effects Ash checkout and branch clutter to one active product worktree without merging into `main` or losing exact commit history.

**Architecture:** Keep `integration/effect-ash-foundations` as the unintegrated milestone continuation ref and `feature/cp0014-local-newtype` as its active checkpoint. Remove redundant checkouts, delete only feature refs already reachable through retained history, and rename non-ancestral planning refs into an archive namespace.

**Tech Stack:** Git linked worktrees, local Git refs, Markdown project artifacts

---

## Task 1: Freeze and verify the cleanup inventory

**Files:**

- Inspect: `.git/worktrees/`
- Inspect: `.worktree/*`
- Verify: `docs/decisions/AD-0011-milestone-worktree-lifecycle.md`
- Verify: `docs/tasks/TASK-0023-consolidate-milestone-worktrees.md`

### Step 1: Record the protected refs

From the main checkout, run:

```bash
git rev-parse main
git rev-parse integration/effect-ash-foundations
git rev-parse feature/cp0014-local-newtype
git rev-parse planning/effect-ash-program
git rev-parse planning/effect-kernel-proposal
```

Expected: five full object IDs. Record them in the task progress before closing
the task. The protected IDs are:

```text
main                                      7195500b7a165f8191efa1485e1ca6f4114180fb
feature/cp0014-local-newtype              b5f6c128200aa53e935613b9e2215f5266cf99ee
planning/effect-ash-program               cddb712f24ac7c57da48015227105b57da5b20a2
planning/effect-kernel-proposal           e5f7340dd5e6f88ec883bfb41daf5386ffb27100
```

The integration tip will include the decision, task, and plan commits; record
its value from the command output rather than treating the product baseline
`fa26025` as its administrative tip.

### Step 2: Recheck every scoped worktree

Run:

```bash
git worktree list --porcelain
for ash_path in .worktree/*; do
  printf '%s\n' "$ash_path"
  git -C "$ash_path" status --short
done
du -sh .worktree
```

Expected: all seven scoped worktrees are registered and clean; CP-0014 is the
only active checkpoint. Stop if any status output is non-empty.

### Step 3: Prove completed feature reachability

Run:

```bash
git merge-base --is-ancestor feature/cp0010-method-local-type-parameters main
git merge-base --is-ancestor feature/cp0012-module-newtype integration/effect-ash-foundations
git merge-base --is-ancestor feature/cp0013-effect-kernel integration/effect-ash-foundations
```

Expected: all three commands exit zero. Stop rather than delete a ref if any
command fails.

### Step 4: Verify documentation hygiene

From the integration worktree, run:

```bash
markdownlint --disable MD013 -- \
  docs/decisions/AD-0011-milestone-worktree-lifecycle.md \
  docs/tasks/TASK-0023-consolidate-milestone-worktrees.md \
  docs/plans/2026-09-03-consolidate-milestone-worktrees.md
git diff --check
git status --short
```

Expected: lint and diff checks pass; status is clean after the plan commit.

## Task 2: Remove completed product checkouts and refs

**Files:**

- Remove checkout: `.worktree/cp0010-method-local-type-parameters/`
- Remove checkout: `.worktree/cp0012-module-newtype/`
- Remove checkout: `.worktree/cp0013-effect-kernel/`

### Step 1: Remove the registered worktrees

From the main checkout, run:

```bash
git worktree remove .worktree/cp0010-method-local-type-parameters
git worktree remove .worktree/cp0012-module-newtype
git worktree remove .worktree/cp0013-effect-kernel
```

Expected: each command exits zero without `--force`.

### Step 2: Delete only the now-redundant refs

From the integration worktree, whose current branch contains all three tips,
run:

```bash
git branch -d feature/cp0010-method-local-type-parameters
git branch -d feature/cp0012-module-newtype
git branch -d feature/cp0013-effect-kernel
```

Expected: Git reports each branch deleted with its former tip. Do not use
`-D`.

### Step 3: Verify retained ancestry

Run:

```bash
git log --oneline --decorate --graph --max-count=12 integration/effect-ash-foundations
git show --quiet dbe4299c9a0dbee72a94e3f7ba5a85663b2653fd
git show --quiet e581296d27966d1f49d74ce7b7f140b2885100ba
git show --quiet 378a39cf17ef16c8917051c07f6be5c54e0f1baa
```

Expected: the completed commits remain readable through retained history.

## Task 3: Archive superseded planning refs

**Files:**

- Remove checkout: `.worktree/effect-ash-program/`
- Remove checkout: `.worktree/effect-kernel-proposal/`

### Step 1: Remove the clean planning worktrees

From the main checkout, run:

```bash
git worktree remove .worktree/effect-ash-program
git worktree remove .worktree/effect-kernel-proposal
```

Expected: both commands exit zero without `--force`.

### Step 2: Move the exact refs into the archive namespace

Run:

```bash
git branch -m planning/effect-ash-program archive/planning/effect-ash-program
git branch -m planning/effect-kernel-proposal archive/planning/effect-kernel-proposal
```

Expected: the active `planning/` names disappear and two `archive/planning/`
names appear.

### Step 3: Verify object identity

Run in the same shell that recorded Task 1 values:

```bash
test "$(git rev-parse archive/planning/effect-ash-program)" = \
  cddb712f24ac7c57da48015227105b57da5b20a2
test "$(git rev-parse archive/planning/effect-kernel-proposal)" = \
  e5f7340dd5e6f88ec883bfb41daf5386ffb27100
git branch --list 'planning/*' 'archive/planning/*' --verbose --no-abbrev
```

Expected: both identity checks exit zero; only the two archive names print.

## Task 4: Close the maintenance transition

**Files:**

- Modify, then remove: `docs/tasks/TASK-0023-consolidate-milestone-worktrees.md`
- Modify: `docs/tasks/README.md`
- Remove: `docs/plans/2026-09-03-consolidate-milestone-worktrees.md`

### Step 1: Record the verified result

Before removal, update TASK-0023 progress with the protected object IDs,
removed paths and refs, archive names, disk-use result, and verification
outcomes. Record deviations instead of silently changing the design.

### Step 2: Remove temporary transition artifacts

Remove TASK-0023 and this plan, and remove TASK-0023 from the active-task index.
Retain AD-0011 and its decision-index entry.

### Step 3: Verify the retained integration diff

Run:

```bash
markdownlint --disable MD013 -- docs/decisions docs/tasks/README.md
git diff --check
git diff --name-only fa26025..HEAD
```

Expected: checks pass, and the final command lists only:

```text
docs/decisions/AD-0011-milestone-worktree-lifecycle.md
docs/decisions/README.md
```

### Step 4: Commit transition cleanup

Run:

```bash
git add docs/tasks/README.md
git add -u docs/tasks/TASK-0023-consolidate-milestone-worktrees.md \
  docs/plans/2026-09-03-consolidate-milestone-worktrees.md
git commit --no-gpg-sign -m "docs: close worktree consolidation"
```

Expected: the task and plan leave the integration tree while their history
remains reachable.

## Task 5: Remove the idle integration checkout and verify the final topology

**Files:**

- Remove checkout: `.worktree/effect-ash-foundations/`

### Step 1: Recheck the final integration checkout

From the main checkout, run:

```bash
git rev-parse integration/effect-ash-foundations
git -C .worktree/effect-ash-foundations status --short
```

Expected: the final integration object ID prints and the worktree is clean.
Record that ID for the final comparison.

### Step 2: Remove the registered integration worktree

Run:

```bash
git worktree remove .worktree/effect-ash-foundations
```

Expected: the command exits zero without `--force`.

### Step 3: Verify the final worktree and ref topology

Run:

```bash
test "$(git rev-parse main)" = \
  7195500b7a165f8191efa1485e1ca6f4114180fb
test "$(git rev-parse feature/cp0014-local-newtype)" = \
  b5f6c128200aa53e935613b9e2215f5266cf99ee
git rev-parse integration/effect-ash-foundations
test "$(git rev-parse archive/planning/effect-ash-program)" = \
  cddb712f24ac7c57da48015227105b57da5b20a2
test "$(git rev-parse archive/planning/effect-kernel-proposal)" = \
  e5f7340dd5e6f88ec883bfb41daf5386ffb27100
git worktree list --porcelain
find .worktree -mindepth 1 -maxdepth 1 -type d -print
git branch --list --verbose --no-abbrev
git tag --list
git status --short --branch
du -sh .worktree
```

Expected:

- all object identity checks exit zero;
- `.worktree/cp0014-local-newtype` is the only checkout under `.worktree/`;
- main, CP-0014, integration, and both archive refs remain;
- no completed feature or active planning refs remain;
- external detached worktrees remain registered;
- tags are unchanged; and
- the main checkout is clean and still on `main`.
