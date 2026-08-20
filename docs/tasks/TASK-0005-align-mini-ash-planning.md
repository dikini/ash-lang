# TASK-0005: Align Mini-Ash Planning

- ID: `TASK-0005`
- Status: active
- Related: [DN-0015: Mini-Ash Phase](../design/DN-0015-mini-ash-phase.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

This task began from the following state:

- DN-0015 defines the current informative phase structure and evidence model.
- The trajectory presented Core as independent of the Mini-Ash corpus and
  linked the nucleus only to DN-0001.
- The Core and parser notes did not route their experiments through DN-0015.

## Work

- Align the trajectory dependencies and next evidence with DN-0015.
- Route Core and parser research through the growing Mini-Ash corpus.
- Preserve all unresolved language, specification, parser, and Core choices.
- Do not create corpus semantics, disposable prototypes, architectural
  decisions, change proposals, or product code.

The execution steps are in the
[implementation plan](../plans/2026-08-20-align-mini-ash-planning.md).

## Progress

The trajectory now routes Mini-Ash and its component research through the
growing evaluation corpus. Core and parser experiment routes link DN-0015 and
now require diagnostic comparison criteria. Repository and documentation checks
pass.

## Verification

- The trajectory routes Mini-Ash, Core, parser, and specification-method work
  through the evidence dependencies described by DN-0015.
- DN-0002 and DN-0003 link DN-0015 and use its growing corpus for comparisons.
- Current artifacts continue to label unresolved choices accurately.
- Changed Markdown passes lint and relative-link inspection.
- `cargo xtask verify` and `git diff --check` pass.

## Discoveries

- The current design notes already contain Core and parser comparison questions
  sufficient for this planning alignment; they needed a shared corpus route
  rather than new architecture.
- Aligning the plan did not require an accepted semantic or architectural
  choice.

## Deviations

- Review tightened the recorded evidence wording to distinguish required
  diagnostic comparison from completed diagnostic evidence.
