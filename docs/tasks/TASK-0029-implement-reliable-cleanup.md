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

Step 3 permits bounded parallel work: the runtime reviewer owns only
`src/eval/machine.rs` for the consumed-clause association regression and fix,
while the implementation writer owns inference and other files. The latter
retains the sole Cargo permit. They exchange explicit file release and test
requests; all writers freeze for architecture scans. This changes coordination,
not scope or acceptance requirements.
That exception is now closed: the regression passed after its observed failure,
and `machine.rs` ownership returned to the implementation writer.
While row recomputation is corrected, a medium-reasoning test writer owns only
new `tests/cleanup_reporting.rs` for independent ordinary reporting variants.
The implementation writer still owns Cargo and every other product/test file;
the same scan freeze and explicit handoff rules apply.
The reporting writer has returned that file after its first run passed all
eight tests. The implementation writer again owns all product/test files.
The implementation writer subsequently released only new
`tests/cleanup_partial_acquisition.rs` to the medium-reasoning reporting writer
for the abandoned-later-initializer witness. Cargo and all other product/test
files remain with the implementation writer; the same handoff rules apply.
Parent also received and returned `tests/spec_examples.rs` for one exact
documented cleanup CLI test, reusing its existing temporary-file guard. No
parallel Cargo commands were run.
The partial-acquisition file has also returned after its first test run passed;
the implementation writer again owns every product/test file and Cargo.
For the remaining acceptance checks, the writer released only
`src/core/validate.rs` to the high-reasoning typed-scope agent for independent
abandonment authority and validation-budget tests. Runtime and row-solving
implementation, all other files and Cargo remain with the primary writer.
That agent returned `validate.rs` with three new authority/budget tests for
the primary writer's first run; all product/test files are again under one owner.
The writer then released only new `tests/cleanup_interactions.rs` to the
medium-reasoning reporting agent for the remaining source interaction witnesses.
All other files and Cargo stay with the primary writer.
That file returned with five tests covering ten programs, including normal and
discarded open-row lacks pairs. Its first execution is pending; the primary
writer again owns all product/test files and Cargo.
Parent briefly received and returned `src/core/validate.rs` for one duplicate
cleanup-acquisition witness; no other product file or Cargo ownership changed.

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
- Syntax checkpoint `390708e` passed semantic and Rust/resource reviews, 1,235 focused
  top-level tests plus three subprocess rechecks, strict Clippy and formatting.
  The plan records exact depth and small-stack evidence. That checkpoint left
  resolution fail-closed pending typed support; full CP-0019 implementation
  remains open.
- Typed ownership and normal execution passed semantic and Rust/resource reviews.
  Final focused regressions passed 1,496 top-level tests plus seven subprocess
  rechecks; all 32 architecture tests, strict all-target Clippy, formatting and
  diff checks passed. The retained small-stack bound is unchanged. The plan
  records the contextual-row and stack corrections.
- Owned abandonment, effectful discard rows, closing-position interpreter checks
  and the full reporting contract are implemented and verified. Corrections
  preserve the retained stack bounds and independently validated least row
  replay. Semantic, Rust/resource and bounded correction reviews passed.
- Fresh full `CARGO_INCREMENTAL=0 cargo xtask verify` exited 0: 2,545 top-level
  tests plus eight logged subprocess rechecks, all 32 architecture checks,
  strict Clippy and warnings-denied rustdoc passed. Markdown, whitespace,
  local-link and notation/authority checks passed. Evidence is retained in
  [the report](../design/effect-ash/reliable-cleanup-evidence.md); the execution
  log is `/tmp/ash-cleanup-step3-full-verify-complete-20260908.log`.
- Remaining lifecycle work: retain this complete product checkpoint, remove
  transition artifacts, perform the unsigned local integration and verify the
  merged checkout, then remove the clean feature worktree and branch.

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

The exact reporting example initially failed parsing because its final match
arm put a line end directly after `=>`. CP-0019's example now places the same
expression on that line, following existing syntax. No language rule or
acceptance result changed; the test retains the corrected complete program.

Moving the checkout preserved cached test binaries with the old absolute source
path. The first baseline exposed this in architecture tests; source files were
unchanged. Ash package artifacts were cleared and the full baseline restarted.

The proposal's captured-handler restriction and distinction between
invocation attempt and successful release remain explicit acceptance boundaries.

## Deviations

Core forgery and runtime preflight/failure probes are colocated with their
owning modules rather than duplicated in new integration files; public
end-to-end cleanup tests remain separate. Required evidence is unchanged.

The 11-unit milestone weight is a relative forecast, not consumed tokens
or a numeric execution allowance. Return semantic gaps to CP-0019 rather than
substituting an easier final contract.
