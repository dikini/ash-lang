# TASK-0063: Host-default Store close

- ID: `TASK-0063`
- Status: active
- Related: [issue #165](https://github.com/dikini/ash-lang/issues/165),
  [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [static semantics](../../spec/static-semantics.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

Preserve actual Store work and release checks, source handlers, unknown external
calls and the independent linked-Core proof. Reuse completed module metadata.

## Work

Fix the first #165 case: a host-default allocation followed by an empty
scheduling turn and normal Store close must compile and execute to `42`. The
separate imported Cell guard case remains outside this task.

## Progress

The exact public-driver regression on Main `33760b2b` completes source and final
elaboration, then fails the independent Core release check. The candidate keeps
the first Core proof and distinguishes an older ambient allocator from a local
selected provider. The public driver now completes and returns `42`.

## Verification

The scheduling target passed 10 tests and retained-control passed 24, including
allocator-enclosed completion and retained-work, stale-probe and unknown-call
rejections. Five focused guard, handler, work-state and stack-safety tests also
passed at unchanged limits. Formatting and warnings-denied Clippy passed for
the changed Rust targets. Independent review remains before the PR. The next
fresh full workspace checkpoint is the Main integration candidate before merge;
the developer runs it when the PM initiates integration.

## Discoveries

The failing focused Store has a symbolic callable entry with no outer handler
and a separate actual entry with the generated allocator handler. The symbolic
context query yields an opaque RegionView. For an escaped canonical request, the
fresh Store cannot have been captured by its older ambient provider; a selected
local provider still follows its own control. A known host-only view also has
its existing host route. Neither rule changes Pending or Unknown work into
Empty, and intervening requests still expire Probe facts.

A source fixture that puts a Store-driving callback in an inner custom provider
currently fails source admission internally even in its completing variant.
Repairing that separate source-admission case is outside this task. The selected
control route and retained-work negatives are checked independently.

## Deviations

None.
