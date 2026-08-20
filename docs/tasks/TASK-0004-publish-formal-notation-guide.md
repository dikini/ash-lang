# TASK-0004: Publish the Formal Notation Guide

- ID: `TASK-0004`
- Status: active
- Related: [AD-0003: Formal Notation Fences](../decisions/AD-0003-formal-notation-fences.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- AD-0003 accepts the `ebnf` and `sequent` source contracts.
- The railroad renderer does not yet accept `::=`.
- The sequent renderer does not yet accept hyphens in rule or family names.

## Work

- Publish the operational notation contract under `docs/project/`.
- Route authors and documentation reviewers to the contract.
- Verify the contract against AD-0003 and the current renderer implementations.
- Record the renderer conformance gaps without modifying either external
  renderer repository.
- Do not define Ash grammar, typing, or operational semantics in this task.
- Do not add documentation automation.

The execution steps are in the
[implementation plan](../plans/2026-08-20-formal-notation-guide.md).

## Progress

The operational guide now defines both fence formats and the complete alias
vocabulary. Project, writing, and documentation guidance route authors and
reviewers to it. Manual and repository checks pass.

## Verification

- The notation guide defines the accepted `ebnf` and `sequent` source formats
  and complete alias vocabulary.
- Project, writing, and documentation guidance route contributors to the guide.
- Every formal-notation example has an accompanying verbal explanation.
- The guide separates notation from Ash language semantics and renderer
  implementation status.
- Changed Markdown passes lint and relative-link inspection.
- `cargo xtask verify` and `git diff --check` pass.

## Discoveries

- The railroad renderer supports the accepted expression forms but still needs
  `::=` support.
- The sequent renderer supports the accepted inference forms and aliases but
  still needs hyphenated rule and family names.
- Neither external gap prevents unrendered Markdown from remaining readable.

## Deviations

None.
