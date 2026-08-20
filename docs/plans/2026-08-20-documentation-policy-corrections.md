# Documentation Policy Corrections Implementation Plan

<!-- markdownlint-disable MD001 MD036 -->

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Correct the documentation lifecycle, agent routing, and project-index
gaps found after implementing AD-0002.

**Architecture:** AD-0002 remains unchanged. One temporary task authorizes three
focused prose edits, records their verification, and then leaves the current tree
with both correction plans.

**Tech Stack:** Markdown, Markdownlint, Git, and the existing Cargo verification
runner.

---

Use `@superpowers:receiving-code-review` while applying the findings and
`@superpowers:verification-before-completion` before every commit and task
completion.

### Task 1: Authorize the corrections

**Files:**

- Create: `docs/tasks/TASK-0003-correct-documentation-policy.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/trajectory.md`

**Step 1: Confirm that TASK-0003 is unused**

Run:

```bash
! git log --all --name-only --pretty=format: | rg 'TASK-0003'
```

Expected: exit 0 with no matches.

**Step 2: Create the active task**

Create `docs/tasks/TASK-0003-correct-documentation-policy.md`:

```markdown
# TASK-0003: Correct the Documentation Policy

- ID: `TASK-0003`
- Status: active
- Related: [AD-0002: Documentation System](../decisions/AD-0002-documentation-system.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- AD-0002 requires lifecycle rules for every documentation domain.
- The post-implementation review identified three policy and routing gaps.

## Work

- State when obsolete Ash language, tool, and Rust crate documentation leaves the
  current tree.
- Link the documentation policy from the agent context route.
- Describe the full scope of the project-documentation index.
- Do not change AD-0002, Rust code, directory structure, or verification
  automation.

The execution steps are in the
[implementation plan](../plans/2026-08-20-documentation-policy-corrections.md).

## Progress

The correction design is approved and this task is active. No policy correction
has been applied yet.

## Verification

- The Ash language/tool and Rust crate domains have explicit removal rules.
- `AGENTS.md` links directly to the documentation policy.
- The project index describes its current policy scope.
- Changed Markdown passes lint and relative-link inspection.
- `cargo xtask verify` and `git diff --check` pass.

## Discoveries

None.

## Deviations

None.
```

**Step 3: Mark TASK-0003 active**

Replace `No implementation task is active.` in `docs/tasks/README.md` with:

```markdown
- [TASK-0003: Correct the Documentation Policy](TASK-0003-correct-documentation-policy.md)
```

Replace the two-line inactive-task statement in `docs/trajectory.md` with:

```markdown
TASK-0003 is correcting the accepted documentation policy. Other work still
needs enough evidence to authorize implementation.
```

Add this row to the trajectory table:

```markdown
| [Documentation policy corrections](decisions/AD-0002-documentation-system.md) | implementation | AD-0002 | Complete [TASK-0003](tasks/TASK-0003-correct-documentation-policy.md): add missing lifecycle and routing rules. |
```

**Step 4: Verify and commit task activation**

Run:

```bash
markdownlint --disable MD013 -- \
  docs/tasks/TASK-0003-correct-documentation-policy.md \
  docs/tasks/README.md \
  docs/trajectory.md
test -f docs/decisions/AD-0002-documentation-system.md
test -f docs/plans/2026-08-20-documentation-policy-corrections.md
git diff --check
```

Expected: all commands exit 0.

Commit:

```bash
git add docs/tasks docs/trajectory.md
git commit -m "docs: authorize documentation policy corrections"
```

### Task 2: Apply the focused corrections

**Files:**

- Modify: `docs/project/documentation.md`
- Modify: `AGENTS.md`
- Modify: `docs/project/README.md`

**Step 1: Demonstrate the three gaps**

Run:

```bash
! rg -q 'When language or tool behavior ceases to be current' docs/project/documentation.md
! rg -q 'When an API, error behavior, invariant, or safety obligation ceases to exist' docs/project/documentation.md
! rg -q '\[documentation policy\]\(docs/project/documentation.md\)' AGENTS.md
! rg -q 'govern Ash documentation and development' docs/project/README.md
```

Expected: every command exits 0 because the required wording is absent.

**Step 2: Complete the Ash language and tool lifecycle**

Add this paragraph after the update rules in the Ash language and tool section of
`docs/project/documentation.md`:

```markdown
When language or tool behavior ceases to be current, update or remove its
documentation in the same change. Git retains the superseded text.
```

**Step 3: Complete the Rust crate lifecycle**

Add this paragraph after the update rule in the Rust crate section:

```markdown
When an API, error behavior, invariant, or safety obligation ceases to exist,
update or remove its documentation in the same change. Git retains the
superseded text.
```

**Step 4: Link the agent route**

Replace the specification/documentation context item in `AGENTS.md` with:

```markdown
- Specification/documentation: [documentation policy](docs/project/documentation.md),
  current specification, an implemented proposal's semantic delta, tests, and
  decisions that affect wording or structure.
```

**Step 5: Broaden the project-index introduction**

Replace the introductory sentence in `docs/project/README.md` with:

```markdown
These documents govern Ash documentation and development: artifacts,
dependencies, specification discipline, and writing:
```

**Step 6: Verify the focused changes**

Run:

```bash
rg -n 'When language or tool behavior ceases to be current' docs/project/documentation.md
rg -n 'When an API, error behavior, invariant, or safety obligation ceases to exist' docs/project/documentation.md
rg -n '\[documentation policy\]\(docs/project/documentation.md\)' AGENTS.md
rg -n 'govern Ash documentation and development' docs/project/README.md
test -f docs/project/documentation.md
markdownlint --disable MD013 -- AGENTS.md docs/project/README.md docs/project/documentation.md
git diff --check
```

Expected: every `rg` finds one match and all remaining commands exit 0.

**Step 7: Commit the corrections**

```bash
git add AGENTS.md docs/project/README.md docs/project/documentation.md
git commit -m "docs: correct documentation policy gaps"
```

### Task 3: Record verification evidence

**Files:**

- Modify: `docs/tasks/TASK-0003-correct-documentation-policy.md`

**Step 1: Run all verification**

Run:

```bash
cargo xtask verify
markdownlint --disable MD013 -- \
  AGENTS.md \
  docs/plans/2026-08-20-documentation-policy-corrections.md \
  docs/plans/2026-08-20-documentation-system-corrections-design.md \
  docs/project/README.md \
  docs/project/documentation.md \
  docs/tasks/README.md \
  docs/tasks/TASK-0003-correct-documentation-policy.md \
  docs/trajectory.md
test -f docs/project/documentation.md
git diff --check
```

Expected: all commands exit 0.

**Step 2: Inspect the new relative link**

Run:

```bash
test -f docs/project/documentation.md
rg -n '\[documentation policy\]\(docs/project/documentation.md\)' AGENTS.md
```

Expected: the target exists and `AGENTS.md` contains one direct link.

**Step 3: Record progress and discoveries**

Replace `Progress` in TASK-0003 with:

```markdown
The language/tool and Rust crate sections now state when obsolete documentation
leaves the current tree. Agent guidance links directly to the policy, and the
project index describes its full policy scope.
```

Replace `Discoveries` with:

```markdown
- AD-0002 already states the required lifecycle and routing outcomes; the
  correction did not require a new decision.
- The correction required no Rust or verification-runner change.
```

Leave `Deviations` as `None.`

**Step 4: Verify and commit the evidence record**

Run:

```bash
markdownlint --disable MD013 -- docs/tasks/TASK-0003-correct-documentation-policy.md
git diff --check
```

Expected: both commands exit 0.

Commit:

```bash
git add docs/tasks/TASK-0003-correct-documentation-policy.md
git commit -m "docs: record documentation correction verification"
```

### Task 4: Complete TASK-0003

**Files:**

- Remove: `docs/tasks/TASK-0003-correct-documentation-policy.md`
- Remove: `docs/plans/2026-08-20-documentation-policy-corrections.md`
- Remove: `docs/plans/2026-08-20-documentation-system-corrections-design.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/trajectory.md`

**Step 1: Remove completed planning records**

Remove TASK-0003 and both correction plan files. Git history retains the design,
execution steps, and verification evidence.

**Step 2: Restore current-state indexes**

Replace the active task in `docs/tasks/README.md` with:

```markdown
No implementation task is active.
```

Replace the active-task statement in `docs/trajectory.md` with:

```markdown
No implementation task is active. Other work still needs enough evidence to
authorize implementation.
```

Remove the documentation-policy-corrections row from the trajectory table.

**Step 3: Verify the final state**

Run:

```bash
cargo xtask verify
markdownlint --disable MD013 -- \
  AGENTS.md \
  docs/project/README.md \
  docs/project/documentation.md \
  docs/tasks/README.md \
  docs/trajectory.md
! rg -n 'TASK-0003|2026-08-20-documentation.*corrections' docs AGENTS.md
test -f docs/project/documentation.md
git diff --check
git status --short
```

Expected: all checks before `git status` exit 0; no current-tree reference to the
completed task or plans remains; status lists only the intended cleanup changes.

**Step 4: Commit completion**

```bash
git add docs/tasks docs/plans docs/trajectory.md
git commit -m "docs: complete documentation policy corrections"
```
