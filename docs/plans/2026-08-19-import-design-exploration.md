# Import Ash Design Exploration Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Convert the supplied Ash explorations into ten topical, non-normative reboot design notes without losing substantive ideas or implying current semantics or roadmap commitments.

**Architecture:** Preserve the complete inputs in Git history, then adapt them into topic-focused `DN-0005` through `DN-0014`. Each current note distinguishes facts, hypotheses, suggested rules, examples, evidence, and open questions; cross-links carry interactions instead of duplicated explanation.

**Tech Stack:** Markdown, Git, shell-based link and content checks; no project implementation toolchain.

---

### Task 1: Preserve the complete source set

**Files:**
- Temporarily create: `docs/import/ash-surface-function-definitions.md`
- Temporarily create: `docs/import/ash-v1-type-system.md`
- Temporarily create: `docs/import/ash-algebraic-effects-01.md`
- Temporarily create: `docs/import/ash-algebraic-effects-02.md`
- Temporarily create: `docs/import/ash-algebraic-effects-03.md`
- Temporarily create: `docs/import/ash-session-types-stress-tests.md`
- Temporarily create: `docs/import/ash-kind-declarations-and-promotion.md`

**Step 1:** Copy the complete user-supplied files byte-for-byte. Use the `(1)` algebraic-effects file followed by the two continuation files, and the `(1)` kind file. Do not copy the truncated versions.

**Step 2:** Verify checksums and line counts against the download sources.

**Step 3:** Commit the source snapshot so provenance survives removal from the final working tree.

### Task 2: Convert surface function design

**Files:**
- Create: `docs/design/DN-0005-surface-function-definitions.md`
- Modify: `docs/design/README.md`

**Step 1:** Adapt all thirteen sections of `ash-surface-function-definitions.md` into one note covering equational and operational forms, global and local typing boundaries, elaboration, recursion, and syntax alternatives.

**Step 2:** Move general pattern coverage details into cross-references to `DN-0007`; retain only the coverage pressure specific to function clauses.

**Step 3:** Convert syntax and exhaustiveness claims into illustrative candidates and searchable suggested rules. Convert initial implementation obligations into evidence needed for a future proposal.

**Step 4:** Review for topical cohesion, generated commitments, and retained open questions, then commit.

### Task 3: Convert initial type-system design

**Files:**
- Create: `docs/design/DN-0006-initial-type-system.md`
- Create: `docs/design/DN-0007-data-and-pattern-typing.md`
- Create: `docs/design/DN-0008-typed-core-and-elaboration.md`
- Modify: `docs/design/DN-0002-core-representation.md`
- Modify: `docs/design/README.md`

**Step 1:** Map source sections 1–12, relevant v1 non-goals from section 31, and the corresponding rationale/trajectory from sections 34–36 into `DN-0006`. Cover kinds, type algebra, identity/equality, functions, quantification, bidirectional local typing, generalization, recursive bindings, and unification.

**Step 2:** Map sections 13–21 and their evidence cases from section 33 into `DN-0007`. Cover tuples, records, ADTs, constructor payloads, visibility, type-directed patterns, irrefutable bindings, and coverage.

**Step 3:** Map sections 22–30, 32–36, and remaining evidence cases into `DN-0008`. Cover explicit Core polymorphism, structured and decision forms, dialect contracts, direct execution, semantic rule boundaries, constraints/evidence seams, and downstream architectural pressure.

**Step 4:** Replace v1 commitments with first-nucleus candidates, retain downstream features as pressure, link `DN-0008` from `DN-0002`, and remove repeated summaries across the three notes.

**Step 5:** Confirm every source section from the type-system note appears in the section map, then commit.

### Task 4: Convert algebraic-effects design

**Files:**
- Create: `docs/design/DN-0009-effects-handlers-and-continuations.md`
- Create: `docs/design/DN-0010-identities-and-resource-lifetimes.md`
- Create: `docs/design/DN-0011-modules-providers-and-resolution.md`
- Create: `docs/design/DN-0012-coeffects-and-hooks.md`
- Modify: `docs/design/DN-0002-core-representation.md`
- Modify: `docs/design/README.md`

**Step 1:** Reconstruct sections 1–68 from the three source segments. Remove the partial section 23/39 boundaries and all code-fence `id="..."` attributes.

**Step 2:** Map sections 1–6, 34–38.3, 45, and relevant summaries from 64–68 into `DN-0009`. Cover effect APIs versus protocols, row requirements, handlers versus providers, ordered handler composition, continuation modes, and effect-row transformation.

**Step 3:** Map sections 7–11, 23–26, 48–51, 57–59, and identity/lifetime gaps from section 64 into `DN-0010`. Cover typed/runtime identities, creation and removal, ownership, draining, stable bindings, captured identities, and continuation/resource interactions.

**Step 4:** Map sections 19–31, 39–45, 52–59, 62–63, and module/resolution material from 64–68 into `DN-0011`. Cover passive modules, providers, static and dynamic resolution, delayed elaboration, opaque sub-worlds, discovery, loading, and unloading.

**Step 5:** Map sections 12–18, 28–29 where registration/resolution interacts, 40, 42, 46–49, 60–61, and coeffect gaps from 64–68 into `DN-0012`. Cover typed hooks, handler publication, registration, sequential/parallel composition, effectful subscribers, lifetime, and continuation interaction.

**Step 6:** Use cross-links where a section pressures more than one note; do not duplicate long explanations. Mark all effect syntax and architectures as downstream hypotheses. Link relevant future pressure from `DN-0002` without changing its accepted status.

**Step 7:** Confirm all reconstructed source sections are represented, then commit.

### Task 5: Convert stress tests and kind exploration

**Files:**
- Create: `docs/design/DN-0013-session-and-resource-protocol-stress-tests.md`
- Create: `docs/design/DN-0014-finite-kinds-and-promotion.md`
- Modify: `docs/design/README.md`

**Step 1:** Adapt all eighteen session-type sections into `DN-0013`. Preserve it as an evaluation corpus for general typing machinery, not a session-type feature proposal. State explicit success and failure observations for transition reuse, aliasing, discard, branching, recursion, capture, generalization, continuation modes, coeffects, and handler composition.

**Step 2:** Adapt all thirty-one replacement kind-note sections into `DN-0014`. Preserve finite nominal static domains and restricted promotion as hypotheses; keep kind polymorphism, dependent elimination, recursive static data, and general promotion as non-goals of the explored small form.

**Step 3:** Link the two notes to the type, effects, identity, and coeffect notes that supply their context. Preserve namespace, promotion-identity, and richer-shape questions.

**Step 4:** Confirm complete section coverage, then commit.

### Task 6: Integrate navigation and current context

**Files:**
- Modify: `docs/design/README.md`
- Modify: `docs/design/DN-0002-core-representation.md`
- Modify: `docs/design/DN-0003-parser-architecture.md`
- Modify if justified without changing priority: `docs/trajectory.md`

**Step 1:** Group the design index by reboot foundations, immediate architecture, surface/type exploration, and downstream stress/feature exploration. Give each note a one-sentence topic description.

**Step 2:** Link parser work to `DN-0005` as representative provisional syntax pressure and Core work to `DN-0008` and `DN-0009` as representation pressure.

**Step 3:** Do not add downstream features as trajectory nodes. Add links to an existing trajectory row only if they clarify that row without changing maturity, dependencies, or priority.

**Step 4:** Review all `Related` links for useful bidirectional context, then commit.

### Task 7: Remove import-only artifacts and audit

**Files:**
- Remove: `docs/import/`
- Remove: `docs/plans/2026-08-19-import-design-exploration-design.md`
- Remove: `docs/plans/2026-08-19-import-design-exploration.md`

**Step 1:** Remove the source snapshot and execution plans from the current tree after confirming they exist in Git history.

**Step 2:** Check all relative Markdown links and heading anchors.

**Step 3:** Check design-note IDs against the current tree and Git history.

**Step 4:** Check that every new note contains the informative authority warning, `Status: exploring`, evidence, and open questions.

**Step 5:** Search for `Suggested rule:` to confirm proposed rules are discoverable, and search for code-fence `id=` attributes to confirm they were removed.

**Step 6:** Verify `spec/` is unchanged and no downstream feature became a trajectory commitment.

**Step 7:** Compare the source-section coverage map with the final notes, review the complete diff, and obtain an independent repository review before integration.
