# Finish Modular Ash Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Close Modular Ash through a bounded intrinsic-versus-explicit-library audit, retained closure evidence, and an unsigned milestone tag without changing language semantics.

**Architecture:** Keep the current specification and accepted decisions as the authority. Compare one retained intrinsic with one operation expressed through an explicit library interface across the admitted-program, typed-elaboration, diagnostic, Core, evaluator, maintenance, and resource/ownership boundaries. Retain reports for the comparison and closure; remove this plan and its owning task after those reports are retained.

**Tech Stack:** Ash specification and documentation, Rust workspace checks, `cargo xtask verify`, focused Rust tests, Markdown lint, Git.

---

## Guardrails

This plan belongs to [TASK-0014](../tasks/TASK-0014-finish-modular-ash.md)
and has no independent authority. Tasks and plans do not define Ash semantics.
If the audit finds a semantic discrepancy, stop that line of work and return to
proposal or design work. Do not add `lib-ash` or `pack-ash` mechanisms, a
prelude or implicit imports, an operator rewrite, module signatures, reexports,
packages, caches, object linking, or interface extensions.

### Task 1: Establish paired audit witnesses

**Files:**

- Modify: the focused current Rust tests and evidence inputs selected by the audit
- Create: the retained core-versus-library report path selected by the audit

**Step 1: Select one retained intrinsic and one explicit-library-interface operation.**

Record why each is representative and which existing specification obligations
govern it. Do not choose a case that requires new syntax or interface
mechanisms.

**Step 2: Write the focused failing behavioral witness.**

Add paired positive and negative cases that expose the same intended
observation and preserve the existing admission, typing, and diagnostic
boundaries.

**Step 3: Run the focused witness to confirm the expected failure.**

Run the smallest owning Rust test command. Record whether the failure exposes
missing evidence or an unauthorized semantic discrepancy.

**Step 4: Make the minimum authorized implementation or evidence change.**

Do not change `spec/` or decide new semantics. If current behavior already
satisfies the witness, retain the witness and report without changing product
code.

**Step 5: Rerun focused checks.**

Run the owning tests and the relevant compiler path. Confirm paired results,
structured diagnostics, Core validation, and evaluator observations.

**Step 6: Review this increment.**

Perform an independent specification review against `spec/`, then an
independent code-quality review of the changed implementation and evidence.
Correct only confirmed non-semantic defects.

### Task 2: Compare boundaries and reconcile proven stale material

**Files:**

- Modify: only audit-proven unused or stale machinery or evidence
- Modify: the retained core-versus-library report

**Step 1: Compare every required boundary.**

For the paired witnesses, document admission, typing, diagnostics, Core,
evaluation, maintenance sites, and resource and ownership consequences.

**Step 2: Identify removal candidates.**

Name the evidence that proves a candidate unused or stale. Reject candidates
whose removal would change current behavior or retained evidence.

**Step 3: Write a focused failing regression before each behavioral cleanup.**

For each cleanup that could affect behavior, add its focused witness and run it
to establish the failure before editing implementation.

**Step 4: Apply the smallest reconciliation and rerun focused checks.**

Remove or simplify only the proven candidate. Recheck the witness, affected
validation, diagnostics, and evaluation paths.

**Step 5: Review this increment.**

Perform an independent specification review, then an independent code-quality
review. Return any semantic discrepancy to proposal or design work.

### Task 3: Retain closure evidence and complete verification

**Files:**

- Create: retained core-versus-library report
- Create: retained Modular Ash closure report
- Modify: `docs/trajectory.md` and relevant evidence indexes only as required

**Step 1: Write the core-versus-library report.**

Retain the paired-witness results, all required boundary comparisons, rejected
cleanup candidates, accepted simplifications, resource and ownership findings,
and exclusions.

**Step 2: Write the Modular Ash closure report.**

State what was retained, simplified, and intentionally excluded. Link the
comparison report and the existing passive-module and interface evidence.

**Step 3: Run the full verification suite.**

Run `cargo xtask verify`, the available Markdown linter for changed documents,
manual relative-link inspection, and `git diff --check`.

**Step 4: Conduct final reviews.**

Conduct an independent specification review of the reports and a separate
code-quality review of all changes. Resolve only non-semantic findings.

### Task 4: Clean up and retain the milestone checkpoint

**Files:**

- Delete: `docs/tasks/TASK-0014-finish-modular-ash.md`
- Delete: `docs/plans/2026-08-25-finish-modular-ash.md`
- Modify: task and trajectory indexes as required

**Step 1: Remove temporary project-management artifacts.**

After the retained closure reports exist, remove the completed task and its
plan, then update indexes so they do not imply that either remains active.

**Step 2: Repeat closure checks.**

Run the full verification suite, Markdown lint, manual link review, and
`git diff --check` after cleanup.

**Step 3: Commit and tag without signing.**

Create the closure commit with `git commit --no-gpg-sign`, create an annotated
unsigned `modular-ash` tag, and verify the commit and tag signature state.

**Step 4: Leave the branch unmerged.**

Confirm the branch contains the closure checkpoint and remains unmerged for
separate review and integration.
