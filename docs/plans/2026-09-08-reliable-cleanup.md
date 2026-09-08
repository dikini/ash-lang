# Reliable Cleanup Implementation Plan

> Execution: use subagent-driven development with test-first increments and
> semantic review before Rust/resource review. The user selected autonomous
> execution in this session; no separate execution-choice prompt is needed.

**Goal:** Implement the complete accepted [CP-0019](../proposals/CP-0019-reliable-cleanup.md).

**Architecture:** Extend existing Effect Core ownership and finite capture
relationships. Ordinary application runs saved actions; an explicit bounded
close continuation drains owned captures without replaying their bodies.
Reporting stays ordinary source effects and data, not runtime error machinery.

**Tech stack:** Rust, existing front-end/typed Core/evaluator and Cargo tests.

**Owner:** [TASK-0029](../tasks/TASK-0029-implement-reliable-cleanup.md).

## Execution constraints

One product writer; parent owns docs and unsigned commits. Syntax writer uses
medium reasoning, semantic/proof/runtime writers and reviews high, documentation
audit medium. Cap all reasoning at high. Do not expand agents into duplicate
whole-repository investigations. Reuse focused context and concise handoffs.

Run one Cargo gate at a time and do not edit product/tests during architecture
scans. Keep the actual session handle until terminal; observation timeout does
not authorize restarting a live process. Full baseline and final gates remain
mandatory; intermediate focused gates target changed boundaries.

## Progress

- [x] Fresh full baseline gate.
- [x] 1. Syntax/projection with explicit fail-closed staging.
- [x] 2. Typed, authenticated cleanup scopes and normal execution.
- [ ] 3. Owned abandonment, cleanup rows and interpreter compatibility.
- [ ] 4. Full interaction/resource corpus and specification.
- [ ] 5. Final reviews, verification, transition cleanup and local integration.

## 1. Syntax and projection

Files: `src/lexer/token.rs`, `src/lexer/mod.rs`, `src/parser/mod.rs`,
`src/parser/grammar.rs`, `src/parser/expression.rs`, `src/parser/project.rs`,
`src/surface.rs`, minimal exhaustive staging in `src/resolve.rs`;
new `tests/cleanup_syntax.rs`. Follow the existing registration outer primary and
iterative projection, without a target-effect field. Parse the action with the
full expression entry point, as CP-0019 requires, not registration's narrower
primary initializer. The following block belongs to the cleanup body.

1. Add a real parse/projection witness for an anonymous unit action and body
   returning `42`, using the existing mandatory block line ends; run
   `CARGO_INCREMENTAL=0 cargo test --test cleanup_syntax` and retain RED.
2. Add only the required token, primary grammar, checked CST shape and surface
   action/body carrier. Until typed admission exists, fail closed in resolution
   using the existing stage failure; do not lower cleanup to an ordinary block.
3. Extend tests to primary positions, grouping/nested initializers, complete
   spans, missing parts, keyword collisions and exact structural admission.
   Keep projection/disposal iterative at predecessor depths and stack bounds.
4. Run `cargo fmt --all --check` and
   `CARGO_INCREMENTAL=0 cargo test --lib --test cleanup_syntax --test hooks_syntax
   --test resource_scope_syntax --test parser --test lexer`.
5. Close semantic then Rust/resource review and retain an unsigned checkpoint.

## 2. Typed scopes, independent Core and normal execution

Files: `src/resolved.rs`, `src/resolve.rs`, `src/elaborate.rs`,
`src/core/effect.rs`, `src/core/validate.rs`, `src/core/transform.rs`,
`src/core/capture.rs`, `src/core/capture/control.rs`, `src/core/capture/value.rs`,
`src/eval/machine.rs`; new end-to-end `tests/cleanup_typing.rs`. Keep Core forgery
and runtime preflight/failure tests in their existing owning modules, where they
can inspect private state; do not duplicate that evidence in separate integration
test files. Update `tests/architecture.rs` only for real carriers.

1. Retain RED for a cell-backed trace: initializer once, nested actions append
   inner then outer digits, saved body result unchanged. Pair callback mismatch,
   escaping captures and an action-local handler with successful reporting.
2. Resolve a preceding action binding and scope owner. Context-check anonymous
   actions against `Unit -> Unit` while retaining latent effects. Reuse charged
   lexical binding and type/row ownership rather than a second callback checker.
3. Add the smallest authenticated Effect operation/contract carrying body and
   action relation. Independent validation reconstructs actual binding, action
   type, least effects, origins, dependencies and completion. Both transforms
   preserve and revalidate it; Pure remains closed.
4. Run action by ordinary function application with a saved body value and a
   non-skippable running owner. Prepare acquisition before mutation; normal
   return releases exactly once. Keep unfinished abandonment fail closed until
   step 3; this is temporary staging, not an accepted restricted implementation.
5. Add exact-work/capacity and small-stack normal/failure witnesses at owning
   sites; rerun library and cleanup/effect/resource/hook focused suites, fmt and
   strict Clippy. Close semantic then Rust/resource review before checkpoint.

## 3. Owned abandonment and cleanup effects

Files: step 2's analysis, elaboration, Core and evaluator owners plus relevant
diagnostic rendering; same cleanup tests and affected predecessor tests.

1. Retain CP-0019's exact complete `72211` source as RED, not an easier rewrite.
   Add resource/registration discard positives and unchanged outside-owner
   negative before changing admission.
2. Extend the existing finite control analysis to the selected owned capture
   and contained live captures. Preserve outside-owner completion and mark the
   running close operation non-skippable. Do not seize non-owning associations.
3. Infer each invoked action's cleanup effects at discard. Preserve requirements
   across removed source handlers, actual callbacks, imports, generic coincidence
   and lexical row authority. Reject required captured interpreters at each
   action's closing position; do not reject already-passed body-local handlers.
4. Implement charged preflight and iterative structural draining. Keep builtin
   cells available until their close positions, remove source/generated handlers,
   invoke actions through the same machine, and resume the discarding clause
   only after close completes. No suspended body/suffix or pending transformer runs.
5. Add running-action discard rejection, safe local discard, capture/resume,
   structural order versus acquisition timestamp, nested live captures, same-type
   linked callback tampering and exact partial-failure traces. Validate both
   transforms independently. Migrate only explicitly newly admitted negatives.
6. Run focused gates and strict Clippy; semantic then Rust/resource review;
   retain the complete supported execution increment unsigned.

## 4. Complete corpus and specification

Parent updates all eight CP-named specification/tool files and adds retained
`docs/design/effect-ash/reliable-cleanup-evidence.md`, indexed from design README.
The evidence maps every CLEAN-01–11 row to actual tests and exact observed bounds,
including failed attempts and residual captured-handler/foreign limits.

The product writer fills remaining reporting, generic/import, dependency,
independent-error-effect, stale/duplicate state, exact capacity/retry, deep
teardown and predecessor cases. `tests/spec_examples.rs` must run the exact
documented CP program via the CLI and check `72211 : Int\n` and empty stderr;
the successful-body companion preserves both value and ordered errors.
Reported failures remain explicit ordinary source declarations/adapters.

Do not fabricate exact budgets before measurement, claim all source failure is
automatically reported, or confuse host disposal with source cleanup. Include
the five named downstream pressure checks from CP-0019 in the closing review.

## 5. Completion

Run independent high semantic, high Rust/resource and medium documentation
audits against the entire CP, then:

```text
CARGO_INCREMENTAL=0 cargo xtask verify
markdownlint --disable MD013 -- docs spec
git diff --check
```

Review local links, formal notation, diagnostic ownership, exact examples and
artifact authority. Retain one complete verified product commit before removing
CP-0019, TASK-0029 and this temporary plan with their index entries. Update
trajectory and DN-0028 only to the observed lifecycle state. Recreate integration
checkout, merge explicitly unsigned, verify the merged checkout fully, prove
clean feature ancestry and remove its worktree/branch under AD-0011. Preserve
main dirt, detached pins, remote refs and tags. No main merge/push/tag.

## Execution record

The first baseline failed because cached architecture-test binaries embedded
the old checkout path after the worktree move; production sources were unchanged.
After discarding only Ash package build artifacts with `cargo clean -p ash`,
the fresh full baseline passed: `CARGO_INCREMENTAL=0 cargo xtask verify`, exit 0,
2,470 top-level tests across 71 suites plus six subprocess rechecks, zero
failures, and successful rustdoc.

Step 1 passed semantic and Rust/resource review. The corrected multiline
parse/projection witness failed before implementation and passed afterward.
The focused library, cleanup, hook, resource-syntax, parser and lexer gate
passed 1,235 top-level tests plus three subprocess rechecks; parent reran it
successfully. Strict all-target Clippy, formatting and diff checks passed.
Exact syntax admission is 64 nested cleanup bodies or 127 nested action
initializers; the next depth rejects and fresh retries preserve admission.
Accepted trees project and dispose on a 256 KiB stack. Resolution deliberately
fails closed until step 2; no cleanup execution or complete CP-0019 admission
is claimed by this syntax checkpoint.

Step 2 began with four failing typing/runtime witnesses at the expected
`resolve.internal-state` boundary: initializer/close order and saved result,
callback shape errors, action-local reporting and captured-result escape.
The lexical, syntax, name-resolution, normal checking/execution and Core-validation
specification delta is drafted. Typed/runtime wording remains pending this
increment's verification.

The first normal-execution implementation passed an annotated variant of the
initializer witness. Parent review rejected that weakening: the original
block-returned anonymous action must receive cleanup's expected function context,
as ordinary contextual block/match results do. The original and a contextual
match action now pass through existing checking with an inferred latent row.
Ten focused cleanup cases pass, including capture/resume and the distinction
between safe local discard and skipped armed/running owners. Independent Core,
owning-resource evidence and reviews remain open before the step 2 checkpoint.

The expanded library gate exposed a retained registration proof's 256 KiB stack
overflow. Debugger evidence places it in the existing elaboration dispatcher
during handler lowering, without new recursion or runtime frames. Extracting
only the three added cleanup branches into phase helpers restored the exact
`core::validate::tests::registration_pipeline_and_disposal_fit_a_small_stack`
test: parent and fresh subprocess pass at 24 registrations on 256 KiB. Neither
the predecessor witness nor its stack bound changed.

Semantic review found one further contextual-row defect: both branch orders of
a mixed pure/effectful anonymous match action reject with
`effect.row-union-ambiguous`, while both explicitly annotated controls return
`42`. A scoped worklist accumulator now joins anonymous-body requirements before
solving their common contextual row. Both direct orders and annotated controls
pass, along with named-function invariance and unrelated-body isolation cases.
All 14 cleanup typing/runtime tests pass and semantic re-review passed.
The expanded dispatcher again exceeded the unchanged registration proof's
small-stack bound after this correction; debugger evidence still shows one
dispatcher frame, not new recursion. Extracting the existing function-completion
arm into a helper restored that bound. A separate completion task tried during
diagnosis was removed; pending cleanup progress remains boxed and its completion
helper takes ownership by value. No test depth, stack or resource limit changed.

Step 2 passed semantic and Rust/resource reviews. Runtime evidence includes
actual-loop traces for failure after a first cell write and after a completed
inner action: neither teardown nor failure replays the action or starts the
outer action. Successful observation also checks that no cleanup owner remains.
Final post-Clippy regressions passed 1,496 top-level tests plus seven subprocess
rechecks, including both interface helper suites affected by exhaustive traversal
updates. The full architecture suite passed all 32 tests; its exact manifest
recheck passed after the final mechanical edits. Strict all-target Clippy,
formatting and diff checks passed. The seven specification files describe this
implemented normal-execution checkpoint; armed abandonment remains deliberately
rejected until step 3 supplies the accepted full contract.

Step 3 retained the complete reporting program as a failing test. Its first
failure exposed a proposal formatting error: a line end directly after the
final match arrow. Keeping that unchanged expression on the same line follows
existing syntax without adding a grammar rule. The corrected complete program
now fails at `discard` with `effect.discard-unsafe`, relating the `Stop` request
and inner cleanup owner. Owned-cell and unused-registration examples reach the
same intended ownership rejection. These are failing implementation witnesses,
not completed acceptance evidence.
