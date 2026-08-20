# Align Mini-Ash Planning Implementation Plan

<!-- markdownlint-disable MD001 MD036 -->

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Align Ash's current trajectory and component research routes with the
corpus-led Mini-Ash phase in DN-0015.

**Architecture:** DN-0015 remains informative and owns the phase exploration.
One temporary task updates planning dependencies and links the existing Core and
parser notes to the shared corpus without accepting semantics or architecture.

**Tech Stack:** Markdown, Markdownlint, Git, and the existing Cargo verification
runner.

---

Use `@superpowers:verification-before-completion` before every commit and task
completion.

### Task 1: Authorize the planning alignment

**Files:**

- Create: `docs/tasks/TASK-0005-align-mini-ash-planning.md`
- Create: `docs/plans/2026-08-20-align-mini-ash-planning.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/trajectory.md`

**Step 1: Confirm that TASK-0005 is unused**

Run:

```bash
! git log --all --name-only --pretty=format: | rg 'TASK-0005'
```

Expected: exit 0 with no matches.

**Step 2: Create and link TASK-0005**

Create the active task and this implementation plan. Scope the task to current
planning and component-note routes. Exclude semantic design, decisions,
proposals, experiments, and product code.

Replace `No implementation task is active.` in `docs/tasks/README.md` with:

```markdown
- [TASK-0005: Align Mini-Ash Planning](TASK-0005-align-mini-ash-planning.md)
```

Replace the inactive-task statement in `docs/trajectory.md` with:

```markdown
TASK-0005 is aligning current planning with the Mini-Ash phase. Other work still
needs enough evidence to authorize implementation.
```

**Step 3: Verify and commit task activation**

Run:

```bash
markdownlint --disable MD013 -- \
  docs/plans/2026-08-20-align-mini-ash-planning.md \
  docs/tasks/README.md \
  docs/tasks/TASK-0005-align-mini-ash-planning.md \
  docs/trajectory.md
test -f docs/design/DN-0015-mini-ash-phase.md
git diff --check
```

Expected: all commands exit 0.

Commit:

```bash
git add docs/plans docs/tasks docs/trajectory.md
git commit -m "docs: authorize Mini-Ash planning alignment"
```

### Task 2: Align the development trajectory

**Files:**

- Modify: `docs/trajectory.md`

**Step 1: Confirm the old dependency rows**

Run:

```bash
rg -n '^\| \[Core representation\].*\| none \|' docs/trajectory.md
rg -n '^\| \[Parser architecture\].*initial syntax needs' docs/trajectory.md
rg -n '^\| \[Specification methodology\].*needs of the first language nucleus' docs/trajectory.md
rg -n '^\| \[Small pure functional nucleus\].*speculative' docs/trajectory.md
```

Expected: each command finds one current row.

**Step 2: Replace the four rows**

Use these current-state rows:

```markdown
| [Mini-Ash phase](design/DN-0015-mini-ash-phase.md) | outlined | implementation environment, growing evaluation corpus, accepted specification method, and sufficient component decisions | Develop the first corpus stratum and use it to compare component boundaries without accepting syntax or semantics. |
| [Core representation](design/DN-0002-core-representation.md) | outlined | growing Mini-Ash corpus and downstream representation pressure | Compare typed representations against progressively richer corpus cases; accept an architecture only after invariants, diagnostics, and extension behavior converge. |
| [Parser architecture](design/DN-0003-parser-architecture.md) | outlined | provisional Mini-Ash grammar and diagnostic cases, kept separate from language authority | Compare composable parser organizations on grammar growth, precedence, recovery, spans, and user-facing diagnostics. |
| [Specification methodology](project/specification.md) | outlined | Mini-Ash operational cases and downstream runtime-state pressure | Accept small-step operational semantics as the primary method before substantial normative semantics. |
```

Remove the old `Small pure functional nucleus` row. DN-0015 now owns that
current planning route. Keep the remaining trajectory rows and the warning that
far-future design pressure is not planned inventory.

**Step 3: Verify and commit the trajectory**

Run:

```bash
rg -n '^\| \[(Mini-Ash phase|Core representation|Parser architecture|Specification methodology)\]' docs/trajectory.md
! rg -n '^\| \[Small pure functional nucleus\]' docs/trajectory.md
test -f docs/design/DN-0015-mini-ash-phase.md
markdownlint --disable MD013 -- docs/trajectory.md
git diff --check
```

Expected: four current rows remain, the old nucleus row is absent, the new link
target exists, and lint and whitespace checks exit 0.

Commit:

```bash
git add docs/trajectory.md
git commit -m "docs: align Mini-Ash trajectory"
```

### Task 3: Route Core and parser research through the corpus

**Files:**

- Modify: `docs/design/DN-0002-core-representation.md`
- Modify: `docs/design/DN-0003-parser-architecture.md`

**Step 1: Demonstrate the missing routes**

Run:

```bash
! rg -q 'DN-0015' docs/design/DN-0002-core-representation.md
! rg -q 'DN-0015' docs/design/DN-0003-parser-architecture.md
```

Expected: both commands exit 0 because neither note links DN-0015.

**Step 2: Link DN-0015 from both notes**

Add this relation to the metadata of DN-0002 and DN-0003:

```markdown
[DN-0015: Mini-Ash Phase](DN-0015-mini-ash-phase.md)
```

Keep each metadata line wrapped consistently with the repository's existing
style.

**Step 3: Align the Core experiment route**

Add this paragraph at the start of `Experiments` in DN-0002:

```markdown
Use progressively richer slices of the
[Mini-Ash evaluation corpus](DN-0015-mini-ash-phase.md#corpus-strata). Begin with
the pure features that distinguish representation boundaries. Treat effects,
continuations, and CPS as downstream pressure; use a theoretical account or a
disposable probe only when the pure corpus cannot distinguish a candidate.
```

Add this item to the evidence recorded for each Core candidate:

```markdown
- source-provenance and diagnostic information preserved by each representation;
```

**Step 4: Align the parser experiment route**

Add this paragraph at the start of `Experiments` in DN-0003:

```markdown
Use progressively richer provisional grammar and diagnostic cases from the
[Mini-Ash evaluation corpus](DN-0015-mini-ash-phase.md#corpus-strata). The corpus
is experimental input rather than accepted Ash syntax.
```

Replace the diagnostic experiment item with:

```markdown
- compare specific Elm- and Rust-style diagnostics and recovery for malformed,
  incomplete, and ambiguous input;
```

**Step 5: Verify and commit the routes**

Run:

```bash
rg -n 'DN-0015|Mini-Ash evaluation corpus' docs/design/DN-0002-core-representation.md docs/design/DN-0003-parser-architecture.md
rg -n 'source-provenance and diagnostic information|Elm- and Rust-style diagnostics' docs/design/DN-0002-core-representation.md docs/design/DN-0003-parser-architecture.md
test -f docs/design/DN-0015-mini-ash-phase.md
markdownlint --disable MD013 -- docs/design/DN-0002-core-representation.md docs/design/DN-0003-parser-architecture.md
git diff --check
```

Expected: each note links the corpus, the new comparison criteria appear, and
all checks exit 0.

Commit:

```bash
git add docs/design/DN-0002-core-representation.md docs/design/DN-0003-parser-architecture.md
git commit -m "docs: route component research through Mini-Ash"
```

### Task 4: Verify and record the planning alignment

**Files:**

- Modify: `docs/tasks/TASK-0005-align-mini-ash-planning.md`

**Step 1: Run repository and Markdown verification**

Run:

```bash
cargo xtask verify
markdownlint --disable MD013 -- \
  docs/design/DN-0002-core-representation.md \
  docs/design/DN-0003-parser-architecture.md \
  docs/design/DN-0015-mini-ash-phase.md \
  docs/plans/2026-08-20-align-mini-ash-planning.md \
  docs/tasks/README.md \
  docs/tasks/TASK-0005-align-mini-ash-planning.md \
  docs/trajectory.md
git diff --check
```

Expected: all commands exit 0.

**Step 2: Inspect links and authority boundaries**

Confirm manually:

- every new relative link resolves;
- DN-0002, DN-0003, and DN-0015 remain informative;
- the trajectory does not present syntax, semantics, or architecture as
  accepted;
- no task or trajectory statement defines Mini-Ash behavior;
- the next activity is corpus design and component comparison, not product
  implementation.

Expected: every item holds.

**Step 3: Record progress and discoveries**

Replace `Progress` in TASK-0005 with:

```markdown
The trajectory now routes Mini-Ash and its component research through the
growing evaluation corpus. Core and parser experiments link DN-0015 and include
diagnostic evidence. Repository and documentation checks pass.
```

Replace `Discoveries` with:

```markdown
- The current design notes already contain the necessary Core and parser
  comparison questions; they needed a shared corpus route rather than new
  architecture.
- Aligning the plan did not require an accepted semantic or architectural
  choice.
```

Leave `Deviations` as `None.`

**Step 4: Verify and commit the evidence record**

Run:

```bash
markdownlint --disable MD013 -- docs/tasks/TASK-0005-align-mini-ash-planning.md
git diff --check
```

Expected: both commands exit 0.

Commit:

```bash
git add docs/tasks/TASK-0005-align-mini-ash-planning.md
git commit -m "docs: record Mini-Ash planning verification"
```

### Task 5: Complete TASK-0005

**Files:**

- Remove: `docs/tasks/TASK-0005-align-mini-ash-planning.md`
- Remove: `docs/plans/2026-08-20-align-mini-ash-planning.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/trajectory.md`

**Step 1: Remove completed planning records**

Remove TASK-0005 and its execution plan. Git history retains their authorization,
steps, and verification evidence.

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

Keep the aligned Mini-Ash, Core, parser, and specification-method rows.

**Step 3: Verify the final state**

Run:

```bash
cargo xtask verify
markdownlint --disable MD013 -- \
  docs/design/DN-0002-core-representation.md \
  docs/design/DN-0003-parser-architecture.md \
  docs/design/DN-0015-mini-ash-phase.md \
  docs/tasks/README.md \
  docs/trajectory.md
! rg -n 'TASK-0005|2026-08-20-align-mini-ash-planning' docs AGENTS.md
git diff --check
git status --short
```

Expected: all checks before `git status` exit 0; no current-tree reference to the
completed task or plan remains; status lists only the intended cleanup changes.

**Step 4: Commit completion**

```bash
git add docs/plans docs/tasks docs/trajectory.md
git commit -m "docs: complete Mini-Ash planning alignment"
```
