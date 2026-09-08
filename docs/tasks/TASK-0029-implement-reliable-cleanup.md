# TASK-0029: Implement Reliable Cleanup

- ID: `TASK-0029`
- Status: active
- Related: [CP-0019](../proposals/CP-0019-reliable-cleanup.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [execution plan](../plans/2026-09-08-reliable-cleanup.md)

> This task organizes authorized work. CP-0019 owns the semantic transition;
> this task and its plan do not define language behavior.

## Dependencies

The user accepted CP-0019 and separately authorized full implementation,
requiring frugal work, simple code and subagents with reasoning no higher than
high. Baseline integration tip: `699395f9f646d3bb8bbf3ba642f91aa2fc47f08b`.
The product checkout is `.worktree/reliable-cleanup` on `codex/reliable-cleanup`.
The integration ref remains the continuation anchor while its checkout is moved.
Main's unrelated edits and detached documentation pins must remain untouched.

## Work

Implement all CLEAN-01 through CLEAN-11: scoped actions, effectful checked
discard, recursive owned-capture closure, structural close order, preserved
outside-owner checks, non-skippable running cleanup, position-sensitive
interpreter compatibility, ordinary typed failure reporting, independent Core
authority, exact resources, deep disposal, predecessor migration and tools.

Use one product writer at a time. Medium reasoning covers bounded syntax work
and mechanical documentation checks; high covers semantic ownership changes
and their reviews. Parent owns planning/status/specification, staging and Git.
Reviewers are read-only and do not run competing Cargo commands. Keep reports
short; record actual evidence once rather than repeating broad histories.

Reuse the existing Effect family, capture analysis and explicit evaluator.
No new exception mechanism, error registry, generic ownership framework,
second interpreter, blanket rejection of accepted positives or raised limits.
All commits and local merges are unsigned; do not change signing configuration,
push, tag or merge main.

## Progress

- Authorization recorded; feature checkout moved from the clean integration
  checkout, preserving its ignored build cache and integration ref.
- Fresh full baseline verification passed before product/test edits: 2,470
  top-level tests plus six subprocess rechecks, zero failures, successful
  rustdoc and full `cargo xtask verify` exit 0.
- Syntax increment passed semantic and Rust/resource reviews, 1,235 focused
  top-level tests plus three subprocess rechecks, strict Clippy and formatting.
  The plan records exact depth and small-stack evidence. Resolution fails
  closed pending typed support; full CP-0019 implementation remains open.

## Verification

Each increment retains its failing witness, minimal correction, focused tests,
semantic review and Rust/resource review. Preserve all CP-0019 obligations
across incremental checkpoints; partial staging is not completion.

At closure run `CARGO_INCREMENTAL=0 cargo xtask verify`, Markdown lint with
MD013 disabled, local-link/notation/authority checks and `git diff --check`.
Retain implementation, tests, specification, reviews and verification in one
complete product checkpoint before removing CP/task/plan and index entries.
Then follow [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md):
unsigned explicit local integration, full merged-checkout verification, clean
feature ancestry proof and worktree/branch removal. No main merge or publication.

## Discoveries

Moving the checkout preserved cached test binaries with the old absolute source
path. The first baseline exposed this in architecture tests; source files were
unchanged. Ash package artifacts were cleared and the full baseline restarted.

The proposal's captured-handler restriction and distinction between
invocation attempt and successful release remain explicit acceptance boundaries.

## Deviations

None. The 11-unit milestone weight is a relative forecast, not consumed tokens
or a numeric execution allowance. Return semantic gaps to CP-0019 rather than
substituting an easier final contract.
