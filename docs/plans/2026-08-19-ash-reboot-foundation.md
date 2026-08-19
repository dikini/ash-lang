# Ash Reboot Foundation Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Establish a minimal, coherent repository foundation for the Ash reboot.

**Architecture:** Keep root files navigational, put current language truth in `spec/`, and separate informative and prospective artifacts by role under `docs/`. Preserve unresolved choices as design work rather than selecting an implementation stack or language semantics during bootstrap.

**Tech Stack:** Markdown, Git, and repository-local Codex skills; no compiler or validation toolchain.

---

### Task 1: Preserve bootstrap inputs

**Files:**
- Preserve: `Ash Reboot Foundations.md`
- Preserve: `Bootstrap the Ash Reboot Foundation.md`
- Create: `docs/plans/2026-08-19-ash-reboot-foundation-design.md`
- Create: `docs/plans/2026-08-19-ash-reboot-foundation.md`

**Step 1:** Review both input documents and confirm the repository has no prior conventions or history.

**Step 2:** Commit the input documents and approved plans so later relocation or removal remains recoverable through Git.

### Task 2: Establish navigation and canonical guidance

**Files:**
- Modify: `README.md`
- Create: `AGENTS.md`
- Create: `CONTRIBUTING.md`
- Create: `spec/README.md`
- Create: `docs/project/artifacts.md`
- Create: `docs/project/specification.md`
- Create: `docs/project/writing.md`
- Create: `docs/trajectory.md`

**Step 1:** Write a concise root entry point and separate human and agent entry points.

**Step 2:** State the exact current specification truth and its merge invariant.

**Step 3:** Define artifact authority, stable IDs, lifecycle, and writing guidance without adding a metadata system.

**Step 4:** Record near-term maturity and dependencies, plus only future pressure supported by the foundation note.

### Task 3: Establish artifact templates and seed design notes

**Files:**
- Create: `docs/design/README.md`
- Create: `docs/design/template.md`
- Move and edit: `Ash Reboot Foundations.md` to `docs/design/DN-0001-reboot-foundations.md`
- Create: `docs/design/DN-0002-core-representation.md`
- Create: `docs/design/DN-0003-parser-architecture.md`
- Create: `docs/decisions/README.md`
- Create: `docs/decisions/template.md`
- Create: `docs/proposals/README.md`
- Create: `docs/proposals/template.md`
- Create: `docs/tasks/README.md`
- Create: `docs/tasks/template.md`

**Step 1:** Add minimal metadata and sections specific to each artifact class.

**Step 2:** Preserve the foundation note as informative source material with a stable identity.

**Step 3:** Seed Core and parser notes only from supported design intent, questions, directions, and experiments.

### Task 4: Add project-local agent skills

**Files:**
- Create: `.agents/skills/reconstructing-ash-context/SKILL.md`
- Create: `.agents/skills/designing-ash/SKILL.md`
- Create: `.agents/skills/implementing-ash/SKILL.md`

**Step 1:** Run baseline role scenarios without each skill and record where context or authority is inferred incorrectly.

**Step 2:** Add one concise skill that addresses the observed gaps, validate its frontmatter, then test the same scenario with the skill.

**Step 3:** Finish validation before starting the next skill.

### Task 5: Remove completed bootstrap artifacts and audit

**Files:**
- Remove after preservation: `Bootstrap the Ash Reboot Foundation.md`
- Remove after preservation: `docs/plans/2026-08-19-ash-reboot-foundation-design.md`
- Remove after preservation: `docs/plans/2026-08-19-ash-reboot-foundation.md`

**Step 1:** Review every final file and remove duplicated or non-current material.

**Step 2:** Check all relative Markdown links and all stable artifact IDs.

**Step 3:** Audit each bootstrap requirement against authoritative files and command output.

**Step 4:** Confirm the specification contains no speculative semantics and the design notes remain non-normative.

**Step 5:** Inspect `git diff`, the final tree, and repository status before reporting completion.
