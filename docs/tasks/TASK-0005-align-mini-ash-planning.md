# TASK-0005: Align Mini-Ash Planning

- ID: `TASK-0005`
- Status: active
- Related: [DN-0015: Mini-Ash Phase](../design/DN-0015-mini-ash-phase.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- DN-0015 defines the current informative phase structure and evidence model.
- The trajectory still presents Core as independent of the Mini-Ash corpus and
  links the nucleus only to DN-0001.
- The Core and parser notes do not yet route their experiments through DN-0015.

## Work

- Align the trajectory dependencies and next evidence with DN-0015.
- Route Core and parser research through the growing Mini-Ash corpus.
- Preserve all unresolved language, specification, parser, and Core choices.
- Do not create corpus semantics, disposable prototypes, architectural
  decisions, change proposals, or product code.

The execution steps are in the
[implementation plan](../plans/2026-08-20-align-mini-ash-planning.md).

## Progress

DN-0015 is indexed and this planning-alignment task is active. The trajectory
and component-note routes have not been updated yet.

## Verification

- The trajectory routes Mini-Ash, Core, parser, and specification-method work
  through the evidence dependencies described by DN-0015.
- DN-0002 and DN-0003 link DN-0015 and use its growing corpus for comparisons.
- Current artifacts continue to label unresolved choices accurately.
- Changed Markdown passes lint and relative-link inspection.
- `cargo xtask verify` and `git diff --check` pass.

## Discoveries

None.

## Deviations

None.
