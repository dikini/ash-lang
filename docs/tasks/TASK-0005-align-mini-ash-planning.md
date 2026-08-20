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

The trajectory now routes Mini-Ash and its component research through the
growing evaluation corpus. Core and parser experiments link DN-0015 and include
diagnostic evidence. Repository and documentation checks pass.

## Verification

- The trajectory routes Mini-Ash, Core, parser, and specification-method work
  through the evidence dependencies described by DN-0015.
- DN-0002 and DN-0003 link DN-0015 and use its growing corpus for comparisons.
- Current artifacts continue to label unresolved choices accurately.
- Changed Markdown passes lint and relative-link inspection.
- `cargo xtask verify` and `git diff --check` pass.

## Discoveries

- The current design notes already contain the necessary Core and parser
  comparison questions; they needed a shared corpus route rather than new
  architecture.
- Aligning the plan did not require an accepted semantic or architectural
  choice.

## Deviations

None.
