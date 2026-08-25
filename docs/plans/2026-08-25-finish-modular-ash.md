# Finish Modular Ash Implementation Plan

**Goal:** Close Modular Ash through a bounded intrinsic-versus-explicit-library
audit, retained closure evidence, and an unsigned milestone tag without
changing language semantics.

**Architecture:** The specification and accepted decisions remain the
authorities. Compare one retained intrinsic with one operation expressed
through an explicit library interface at the admitted-program, typed
elaboration, diagnostic, Core, evaluator, maintenance, and resource and
ownership boundaries. Retain the comparison and closure reports, then remove
this plan and its owning task after the retained reports exist.

**Tech Stack:** Ash specification and documentation, Rust workspace checks,
`cargo xtask verify`, focused Rust tests, Markdown lint, Git.

---

## Guardrails

This plan belongs to [TASK-0014](../tasks/TASK-0014-finish-modular-ash.md) and
has no independent authority. Tasks and plans do not define Ash semantics. If
the audit finds a semantic discrepancy, stop that line of work and return to
proposal or design work.

Do not add `lib-ash` or `pack-ash` mechanisms, a prelude or implicit imports,
an operator rewrite, module signatures, reexports, packages, caches, object
linking, or interface extensions. Reconciliation is limited to machinery or
evidence proven unused or stale, and must preserve admitted behavior,
diagnostic ownership, Core validity and shape obligations, and evaluation. Any
finding that would change those boundaries requires new authorization.

### Task 1: Establish paired audit witnesses

**Files:**

- Create: `tests/modular_closure.rs`
- Create: `docs/design/modular-ash/core-library-evidence.md`

**Step 1: Select the paired cases.**

Select one retained Core intrinsic and one explicit-library-interface operation.
Record why both are representative and which current specification obligations
govern them. Do not select a case that needs new syntax or interface machinery.

**Step 2: Establish the new focused witness target.**

Show that `tests/modular_closure.rs` and its paired cases are absent, then add
positive and negative cases that expose the existing intended observation
without changing admission, typing, or diagnostic boundaries.

**Step 3: Run the new witness against current behavior.**

Run:

```bash
cargo test --locked --test modular_closure
```

Record paired results in
`docs/design/modular-ash/core-library-evidence.md`. Existing behavior need not
fail before new audit evidence is added. Return a mismatch to proposal or
design work.

**Step 4: Run affected boundary checks.**

Run:

```bash
cargo test --locked --test architecture --test interfaces --test interface_modules --test interface_validation
```

Confirm the paired cases preserve structured diagnostics, Core validation and
shape obligations, and evaluator observations.

**Step 5: Review this increment.**

Perform an independent specification-and-authority review against `spec/`, then
an independent code-quality review of the test and evidence changes. Correct
only findings within this task's audit scope; return semantic or broader
findings to design, proposal, or new authorization.

### Task 2: Compare boundaries and reconcile proven stale material

**Files:**

- Modify: `docs/design/modular-ash/core-library-evidence.md`
- Modify: only audit-proven stale or unused machinery or evidence named by that report
- Test: `tests/modular_closure.rs` and `tests/architecture.rs`

**Step 1: Compare every required boundary.**

For the paired witnesses, document admission, typing, diagnostics, Core,
evaluation, maintenance sites, and resource and ownership consequences in
`docs/design/modular-ash/core-library-evidence.md`.

**Step 2: Identify reconciliation candidates.**

Name the evidence proving each candidate unused or stale. Reject a candidate
whose removal would change admitted behavior, diagnostic ownership, Core
validity or shape obligations, evaluation, or retained evidence.

**Step 3: Establish an architecture or invariant witness for each candidate.**

Before editing production material, add or extend an architecture or invariant
witness that detects the unwanted retained state. It checks retained
architecture or invariants, not a changed observable behavior. Record the
pre-edit observation and the exact stale-or-unused claim it tests.

**Step 4: Apply the smallest reconciliation and rerun focused checks.**

Remove or simplify only the proven candidate. Run:

```bash
cargo test --locked --test modular_closure
cargo test --locked --test architecture --test interfaces --test interface_modules --test interface_validation
```

Confirm that the cleanup removes the unwanted state while preserving admitted
behavior, diagnostic ownership, Core validity and shape obligations, and
evaluation.

**Step 5: Review this increment.**

Perform an independent specification-and-authority review, then an independent
code-quality review. Correct only findings within proven stale-or-unused
reconciliation scope; return semantic or broader findings to design, proposal,
or new authorization.

### Task 3: Retain closure evidence

**Files:**

- Create: `docs/design/modular-ash/closure.md`
- Modify: `docs/design/modular-ash/core-library-evidence.md`
- Modify: `docs/design/README.md`

**Step 1: Complete the core-versus-library report.**

Retain paired-witness results, all boundary comparisons, rejected candidates,
accepted reconciliations, resource and ownership findings, and exclusions in
`docs/design/modular-ash/core-library-evidence.md`.

**Step 2: Write the Modular Ash closure report.**

Create `docs/design/modular-ash/closure.md`. State what the milestone retains,
what it reconciles, and what it intentionally excludes. Link the
core-versus-library report with existing passive-module and interface evidence.

**Step 3: Link retained evidence from the design index.**

Add both retained reports to `docs/design/README.md` without implying that they
define current Ash semantics.

**Step 4: Review this increment.**

Perform an independent specification-and-authority review, followed by an
independent code-quality review. Correct only in-scope findings; return
semantic or broader findings to design, proposal, or new authorization.

### Task 4: Clean up and retain the milestone checkpoint

**Files:**

- Delete: `docs/tasks/TASK-0014-finish-modular-ash.md`
- Delete: `docs/plans/2026-08-25-finish-modular-ash.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/trajectory.md`

**Step 1: Remove temporary project-management artifacts.**

After retained reports exist, remove the completed task and plan, and update
the task index and trajectory so they do not imply an active task or plan.

**Step 2: Review after lifecycle cleanup.**

Perform an independent specification-and-authority review, followed by an
independent code-quality review. If either finds an in-scope issue, correct it
and repeat both reviews. Return semantic, behavior-changing, or broader
findings to design, proposal, or new authorization.

**Step 3: Repeat final verification.**

Run:

```bash
cargo xtask verify
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Inspect every changed relative link manually. Repeat this verification after
any in-scope correction made during the lifecycle-cleanup review loop.

**Step 4: Commit and tag without signing.**

Create the closure commit and annotated unsigned tag:

```bash
git commit --no-gpg-sign -m "docs: close Modular Ash"
git tag --no-sign -a modular-ash -m "Modular Ash"
```

Inspect the commit and tag objects for the absence of GPG signature headers or
blocks:

```bash
! git cat-file -p HEAD | rg -q '^(gpgsig |-----BEGIN PGP SIGNATURE-----)'
! git cat-file -p refs/tags/modular-ash | rg -q '^(gpgsig |-----BEGIN PGP SIGNATURE-----)'
```

**Step 5: Prove the branch remains unmerged.**

Run:

```bash
git merge-base --is-ancestor main HEAD
! git merge-base --is-ancestor HEAD main
```

The first command proves `main` is an ancestor of the closure commit. The
second proves that the closure commit is not already in `main`; leave the
branch unmerged for separate review and integration.
