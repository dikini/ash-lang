# TASK-0026: Implement Capture and Checked Discard

- ID: `TASK-0026`
- Status: active
- Related: [CP-0016](../proposals/CP-0016-capture-usage-and-checked-discard.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [execution plan](../plans/2026-09-06-capture-checked-discard.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

User-approved explicit discard and inferred capture-summary contract. Start
from integration commit `da3ea62a1eee5642ec16a11210ee643e33d56574` on local
branch `codex/capture-checked-discard`, in `.worktree/capture-checked-discard`.
The clean integration checkout was moved to this path before branching;
the integration ref and unrelated main checkout remain unchanged.

## Work

Implement the accepted proposal through test-driven source/Core/runtime
completion support, inferred capture summaries, independent authentication,
resource tests, specification and reviewed evidence. Keep one product writer.

## Progress

- Design explained and accepted in the task conversation on 2026-09-06.
- Isolated worktree prepared at the exact integration tip.
- Baseline `cargo test --workspace --all-targets` passed with exit status 0
  before product edits, including 979 library tests and the complete integration
  suite. The architecture source guard took 332.76 seconds; the deep-data
  binary took 151.65 seconds. Neither reported a failure.
- High-reasoning read-only agent auditing summary composition; parent owns
  proposal and task preparation.
- Step 1 product writer started after the baseline passed. Capture-summary
  implementation and runtime discard remain pending.

## Verification

Record RED/GREEN commands and their actual outcomes in the task-owned plan.
Run the CP-0016 positive, negative, tamper, transform, budget and deep teardown
corpus, then `cargo xtask verify`. Require independent semantic review before
independent code/resource review. Check changed Markdown links and authority.
Only close transition artifacts after all required evidence is retained.

## Discoveries

Stored closure captures do not describe the obligations carried by a request
made during that closure's call. Request summaries must compose at calls and
respect the nearest handler boundary.

## Deviations

None. The milestone forecast assigns this checkpoint 9 of its notional 100
units. That is a relative forecast, not an elapsed-work measure or a new numeric
authorization. Do not invent spent-unit figures or expand into resource scope.
