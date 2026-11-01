# TASK-0064: Imported Cell guard

- ID: `TASK-0064`
- Status: active
- Related: [issue #165](https://github.com/dikini/ash-lang/issues/165),
  [retained-control and Cell rules](../../spec/static-semantics.md),
  [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md)

> This task organizes work. It does not define Ash semantics.

## Work and progress

Keep the issue's imported Cell guard, two-branch P/Q program and single-branch
control as fixture-only code. Both programs now execute through the public
driver and return `(42, 123456)` on Main `9bf8226d`; the historical
`type.internal` refusal did not reproduce. The cause or exact fixing change is
not established. The shipped scheduling API and compiler remain unchanged.

The existing inline P/Q control and the retained-control and sealed-provider
negatives also pass. The programs exercise the selected provider and owner
identities and the independent linked Core proof.

## Verification and next checkpoint

The affected scheduling, resource-module and retained-control targets passed
12, 17 and 24 tests respectively. Formatting and warning-denied Clippy for the
scheduling target passed. Independent review remains pending.

The last fresh full workspace gate passed on PR #204 head `7f427014`, whose
tree is identical to Main `9bf8226d`. A fresh full workspace gate on the settled
integration candidate remains pending before Main integration; the developer
owns that checkpoint when the orchestrator initiates it.
