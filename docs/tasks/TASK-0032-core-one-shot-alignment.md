# TASK-0032: Align Effect Core with the annotated one-shot calculus

- ID: `TASK-0032`
- Status: active
- Related: [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md),
  [CP-0021](../proposals/CP-0021-local-effects-in-resume-operands.md),
  [DN-0033](../design/DN-0033-direct-effects-and-continuation-capabilities.md),
  [execution plan](core-one-shot-alignment-plan.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

The user authorizes comparison, necessary alignment changes and verification of
validated Effect Core against the completed annotated one-shot M0–M4 calculus.
The accepted Core and evaluator decisions govern implementation boundaries.
DN-0033 governs formal experiments. A demonstrated language change requires a
proposal before product implementation; a repair to current specified behavior
does not change the language contract.

Use GPT-6 Astra for orchestration, analysis and integration, and GPT-6.1 Sol
with medium reasoning for implementation workers. Verify each assignment.

## Work

The stable inventory below measures deliverables, not equal amounts of effort.
Subcase inventories will be recorded in the comparison evidence after inspection.

| Package | Named inventory | Acceptance |
| --- | --- | --- |
| C1 | C1.1 fragment and construct map; C1.2 cleanup comparison; C1.3 direct/bound resume comparison; C1.4 discrepancy classification; C1.5 finite translation/transition inventory | Explicit transitions and reproducible evidence distinguish admission differences, runtime disagreements, representation and missing proofs. |
| C2 | C2.1 typed translation; C2.2 exact identities/signatures; C2.3 lexical resources/capabilities; C2.4 initial admission | Translation constructs the existing structural admission judgments from static input without future-execution assumptions. |
| C3 | C3.1 configuration relation; C3.2 transition simulation; C3.3 observations/ownership; C3.4 capacity and preparation; C3.5 nonvacuity | Actual Core steps have the stated calculus match, including administrative-step justification and progress measure. |
| C4 | C4.1 discrepancy resolutions; C4.2 positive regressions; C4.3 negative regressions | All demonstrated disagreements in the declared fragment are resolved with authority and evidence. |
| C5 | C5.1 integrated theorem; C5.2 coverage/specification records; C5.3 grouped verification; C5.4 independent review | Mechanized model claims, Rust evidence and exclusions remain explicit; checks contain no proof holes or unjustified axioms. |

Start with handlers, requests, sequencing, resume, discard, cells and cleanup.
Classify ordinary constructs, polymorphism, synchronous hooks and native buffers
explicitly. Multishot, escaping continuations, suspension and asynchronous hooks
remain separate targets. A small first example does not reduce the final scope.

## Progress

- Baseline: `124e164`, clean `main`; work uses `codex/core-alignment` in
  `.worktree/core-alignment`.
- Verified orchestrator assignment: `gpt-6-astra`, high reasoning.
- Current specification removes captured source handlers during discard and
  rejects cleanup whose nearest interpreter would be removed. The calculus
  retains captured handlers until lexical unwind reaches them. Comparison must
  first determine whether this difference is observable for validated Core.
- M0–M4 endpoints have been inspected. Their theorem boundary is annotated
  initial admission and constructive calculus execution, not Core admission or
  arbitrary-annotation preservation. Fresh baseline verification passed.
- No C1–C5 deliverable is yet marked integrated.

### Increment 1 local results

- C1.1–C1.5 are recorded in the
  [comparison evidence](../design/direct-effects/one-shot/CORE-ALIGNMENT.md).
  Independent review confirmed the finite inventory: 23 Core node alternatives,
  19 Core frame alternatives, 16 calculus expressions and 32 calculus transition
  families. These counts are coverage inventories, not correspondence proofs.
- Six cleanup comparison tests pass, including exact cell closing order,
  nearest-interpreter rejection, the complete kernel fixture and a pure closure
  retaining a live cell. The complete fixture returns 11 and enters write
  applications 7 then 11, skipping 99.
- CP-0021 is implemented and locally reviewed: five direct/bound/nonempty-row/
  imported-summary resume regressions pass. Independent validation rejects
  missing operand effects, missing continuation effects and inflated rows.
  Focused work-limit and rollback checks pass, along with 172 related runtime,
  resource, hook and cleanup tests. Full `cargo xtask verify` passed, including
  formatting, metadata, build, lint, workspace tests and documentation.
- [CoreClosing](../design/direct-effects/one-shot/CoreClosing.lean) proves exact
  retained-frame order and owner partition for successful discard projection.
  Independent compilation and scope review pass. This is part of C3.2/C3.3;
  callback execution and full configuration simulation remain outstanding.
- C2 workers are constructing the finite Core syntax translation and admission
  for the complete kernel fixture. The callable-support component passed
  independent compilation and scope review and is registered in `check.sh`.
  No general compiler is counted complete yet.
- The cache-aware registered Lean baseline build and recursive audit passed:
  763 modules, 10,622 exact dependency reports and 1,885 local links/anchors.
  Only `propext`, `Quot.sound` and `Classical.choice` occur in the reports.
  New alignment modules receive separate checks before registration.
  A duplicate uncached baseline build was stopped deliberately; its exit 143 is
  not a verification result. No failing proof was bypassed.

| Package | Completed / identified | State | Outstanding | Dependency / next estimate |
| --- | --- | --- | --- | --- |
| C1 | 5 / 5 | Verified and reviewed | Retain findings at integration | Documentation integration pending |
| C2 | 0 / 4 | Syntax and support constructions underway | General static compiler and full admission | First constructions: 1–2 active hours; total awaits fresh-owner clause compiler evidence |
| C3 | 0 / 5 | Closing projection component verified | Complete state relation, transitions and observations | Depends on C2; full estimate unresolved |
| C4 | 3 / 3 for currently demonstrated D2 | Implementation, review and full Rust gate complete | Product checkpoint; future C2/C3 discrepancies may add cases | Documentation integration pending |
| C5 | 0 / 4 | Baseline and current product checks pass | Integrated theorem and final scope audit | Depends on C2–C4 |

## Verification

Use focused Rust regressions and grouped Lean dependency builds during each
increment. At integration run `cargo xtask verify`, the one-shot `check.sh`,
the existing recursive proof/axiom audit, Markdown lint, changed-link checks and
authority review. Inspect theorem statements and dependencies as well as results.
Independent review covers source semantics before code quality and theorem scope.

## Discoveries

Historical proof sections retain old open obligations. Current endpoint code and
the final M0–M4 evidence determine the baseline; historical prose must not reset
completed milestones.

## Deviations

None. Exact fragment and transition inventories remain C1 work.
