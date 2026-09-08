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

During step 3 only, the runtime reviewer may own `src/eval/machine.rs` for the
independent consumed-clause association fix while the primary writer finishes
row inference. Exclusive file ownership is explicit; Cargo remains with the
primary writer and all edits pause for architecture scans. Return that file
before the complete increment's review and gate.
The bounded fix has returned its file; the primary writer again owns all
product and test files.
A second bounded exception assigns only new `tests/cleanup_reporting.rs` to a
medium test writer while the primary writer corrects row recomputation. Cargo
remains serialized; no production code is shared between writers.

Run one Cargo gate at a time and do not edit product/tests during architecture
scans. Keep the actual session handle until terminal; observation timeout does
not authorize restarting a live process. Full baseline and final gates remain
mandatory; intermediate focused gates target changed boundaries.

## Progress

- [x] Fresh full baseline gate.
- [x] 1. Syntax/projection with explicit fail-closed staging.
- [x] 2. Typed, authenticated cleanup scopes and normal execution.
- [x] 3. Owned abandonment, cleanup rows and interpreter compatibility.
- [x] 4. Full interaction/resource corpus and specification.
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

The first control/runtime increment passes the reporting, retained-cell,
recursive owned-capture, structural-order and closing-position handler pairs.
This is still incomplete: discard row annotations remain empty. A clause-local
handler around `discard`, reached through a forward helper, retains a separate
`effect.handler-missing-input` failure. A late row correction cannot repair an
earlier handler check, and partial graph queries lack forward/recursive binding
relationships. Existing row union/removal and Core construction are eager.
Implementation is therefore adding scoped cleanup-dependent row obligations,
solved from complete capture relationships before final row checking; unrelated
row operations remain eager. This is an implementation dependency, not a new
language rule or permission to weaken independent Core validation.

Early runtime review found that a consumed clause still carries a registration
completion association. The first discard preflight inspected that association
only for clauses with live captures. A direct machine test failed because the
invalid discard returned success, then passed after collecting associations
from every clause. Rejection now retains the capture, accounting, outside
pending invocation and armed action without starting cleanup. This closes that
specific review finding, not the full abandonment resource gate.

Scoped row integration exposed two publication boundaries. Row solutions must
use the existing authenticated solution path, and pending node-row inference
must force the existing Core rewrite pass even when node value types contain
no inference. Without the latter, strict normalization skipped the rows and
global recomputation failed on unresolved tails. After correcting the flag,
all seven abandonment tests pass, including clause-local handling through both
forward and recursive helpers. Imported/generic row authority, remaining
resource evidence and full regression gates are still open.

The broader focused gate passed all 14 normal cleanup and eight reporting tests.
It exposed predecessor expectations for now-owned clause captures and a missed
result-finalization boundary. Migration review retains outside resource and
registration negatives, and requires an opaque-callback countercheck whose hidden
cleanup would require a removed handler. A two-instantiation generic cleanup
test failed because specialized rows were unioned under one lexical node ID;
the correction must retain lexical inference and separate occurrence checks,
including imported graph identity and actual nested-closure value flow.

The implementation writer reports a later focused gate with abandonment 10/10,
reporting 8/8 and normal cleanup 14/14. The broader suites returned effect
20/23, hooks 22/25 and resource scopes 58/61: all nine failures accepted programs
whose old expectations required rejection. Each fixture still requires an
ownership-boundary review before migration; outside-owner negatives remain
unchanged. These terminal counts were not retained in a log and must be replaced
by the next logged regression gate before final acceptance.

A direct builder witness then exposed unfinished cleanup equations escaping
source construction. The writer added a finish guard after that observed
failure. The writer reports both pending-builder tests passed; this guard and
the row-only rewrite flag protect distinct construction boundaries. The next
retained regression gate must include them.

The next retained focused gate passed 143 top-level tests plus one resource
subprocess recheck, including all nine reviewed predecessor migrations and the
new abandoned-initializer witness. Parent inspected terminal output in
`/tmp/ash-cleanup-step3-focused-20260908.log`; the unused completion-owner warning
remains a strict-lint obligation. The initializer witness passed its first run,
not an observed behavioral red-to-green cycle. Its file returned to the primary
implementation writer. Exact CLI and owning runtime/Core budget checks remain
separate pending gates.

The owning discard-preparation witness passed exact, one-short and fresh-retry
checks with two cleanup owners and a nested live capture. Parent inspected
`/tmp/ash-cleanup-step3-preflight-20260908.log`. A later four-test runtime gate
exposed a stack overflow in the new 24-owner drain witness at the unchanged
256 KiB bound. The failure requires stage-specific diagnosis; it does not
authorize reducing depth or increasing the predecessor stack limit. Independent
Core tests proceed under a disjoint-file handoff while runtime diagnosis stays
with the primary writer.

Parent inspected the seven-test cleanup Core gate in
`/tmp/ash-cleanup-step3-core-authority-20260908.log`: all passed, including the
three new abandonment authority/budget witnesses. They cover linked callback
mutation across generic handler coincidence, forged discard rows through both
transforms and direct capture reconstruction, and exact/one-short/fresh capture
work. These were first-run passes; they do not close the remaining interaction,
deep-stack, strict-lint or full-verification obligations.

The deep test now passes unchanged at 24 owners and 256 KiB, including its
subprocess (`/tmp/ash-cleanup-step3-deep-frame-20260908.log`, inspected by parent).
After request-operand resolution moved onto its existing worklist, the next
trace identified overlapping elaboration dispatch frames during handler-body
and then clause checking. Reusing handler-body scheduling and extracting the
ordinary task step leaves a small driver active during clause reentry. This
removes the measured overlap without a new handler state machine. Stronger
partial-drain marker assertions were added afterward and still require rerun.

The exact documented CLI test passed after its extraction retained the source
block's final newline (`/tmp/ash-cleanup-step3-cli-20260908.log`, inspected by
parent). This was a harness correction, not a semantic change. The first
interaction run passed publication abandonment and both cell/source and hook
closing-position pairs. Recursive mixed-scope work exhaustion remains under
diagnosis. The discarded open-row positive omitted a necessary `Stop` exclusion:
body/action row union rejects before deferred discard inference. Correcting that
fixture must retain missing-exclusion negatives rather than weaken row checking.

The corrected discarded callback row explicitly excludes both `Adjust` and
`Stop`. It passes the earlier body union and now fails at `internal.core-build`
(`/tmp/ash-cleanup-step3-explicit-lacks-20260908.log`). This is a separate
construction failure under diagnosis; no unknown-request matching change is
justified by it alone. Parent also added an unrun duplicate-acquisition witness:
two cleanup scopes share one callback binding after both the owner field and
action reference are changed consistently, checked before and after both
transforms. The primary writer retains its first execution and all Cargo work.

The combined recursive mixed-order witness exceeded capture discovery's budget.
The two independent CLEAN-02 obligations now have separate passing witnesses:
overlapping activations of one recursive cleanup site return `21`, and mixed
cell/registration/action closing order returns `110`. Parent inspected
`/tmp/ash-cleanup-step3-recursive-split-20260908.log` and
`/tmp/ash-cleanup-step3-mixed-split-20260908.log`. The report retains how to
reproduce the combined `231110` case and its unproved admission; no limit or
analyzer change was made to admit it.

Instrumentation confirmed recomputation erased the application's lexical lacks
before cleanup row union. Preserving only same-tail lacks while recomputing
known effects moves the corrected source past Core construction to
`effect.cleanup-context` (`/tmp/ash-cleanup-step3-lacks-preserved-20260908.log`).
Independent forall validation remains unchanged. The new failure exposes the
separate opaque-request exclusion path; the positive is not yet accepted.

The corrected open-row test now passes its positive and missing-exclusion
negative cases (`/tmp/ash-cleanup-step3-lacks-control-20260908.log`, inspected by
parent). Opaque labels retain the substituted row and distinguish exclusions
during interning; only exact, non-ambiguous excluded handlers are skipped.
A separate observed regression shows failed unification retaining one extra
cleanup equation. Transaction rollback and broader authority checks remain
pending before this correction is considered a stable checkpoint.

The consolidated gate subsequently passed 34 top-level tests and two subprocess
rechecks without warnings, including transaction rollback, duplicate acquisition,
opaque exclusions and the six interaction witnesses. Independent semantic and
Rust/resource reviews passed. The first full gate passed format, build and strict
Clippy but exposed eight predecessor expectations changed by owned closure.
Reviewed migrations preserve outside-owner, running-completion and malformed
accounting negatives. All 1,167 library tests now pass without warnings
(`/tmp/ash-cleanup-step3-lib-migrations-final-20260908.log`, inspected by parent).
The inventory scan found 14 missing fields and no stale fields. The writer added
those fields and started the fresh full gate at
`/tmp/ash-cleanup-step3-full-verify-final-20260908.log`. Its completion remains
required; this entry does not close CP-0019 or authorize publication.

That full gate terminated with exit 1 after strict Clippy, library tests and all
32 architecture checks passed. The next failure was a stack overflow in
`tests/data_and_adts.rs`, before that suite completed. The writer retains sole
Cargo and product ownership and is isolating the test and call path. No stack
or depth bound is changed, and the gate does not establish full acceptance.

The isolated failure is
`admitted_nested_patterns_complete_the_full_pipeline_on_a_small_stack`, whose
bound remains 512 KiB. The debugger shows nested match resolution repeatedly
stacking `visit_expression` and `resolve_work_inner`; their measured frames are
`0x71e8` and `0xda88` bytes. The writer's first bounded correction extracts the
new `FinishPerform` construction from the work driver to remove its large
temporaries from each recursive entry. The same test and frame measurement must
verify that hypothesis before acceptance; no match-state-machine rewrite is
authorized by this observation alone.

The first extraction did not restore the 512 KiB witness. The work-driver
frame fell from `0xda88` to `0xd0c8` bytes, but the debugger still shows the same
nested-match call path. The next diagnosis examines the added work-item payload
before choosing another correction; this is a retained failed hypothesis, not
a passing stack result.

Layout measurement ruled out work-item growth: pre-existing `FinishResource`
still determines the 208-byte enum size. Routing Match directly from the work
driver to a helper containing its original arm removes the ordinary expression
dispatcher from recursive matches. The helper frame measures `0x19c8` bytes,
versus the displaced `0x71e8` frame; the work driver measures `0xd0f8`.
The unchanged 512 KiB witness now passes
(`/tmp/ash-cleanup-step3-adt-match-dispatch-20260908.log`, inspected by parent).
The extraction preserves scrutinee/arm order, scope truncation and owned buffers.
A bounded independent review passed with no findings: no shared validation or
charge is bypassed, and ownership guards and error rollback are preserved.
The writer started the full library plus all 73 nonarchitecture integration
targets at `/tmp/ash-cleanup-step3-all-nonarchitecture-20260908.log`, before
another fresh full gate. Those wider results remain required.

The sweep passed all 32 data/ADT tests, including both retained stack bounds,
and 45 diagnostic tests. It then exposed one obsolete Effect Core expectation:
a nonempty forged discard row with no owned action still rejects, but now at
independent effect-row validation (`EffectRow`) rather than the predecessor
blanket empty-row check (`Resume`). Review approved changing only that expected
reason; the forged fixture and every unrelated owner/type/exact-once case stay
unchanged. The writer continues the full nonarchitecture sweep with
`--no-fail-fast` so later failures are not hidden by the first target failure.

The remaining-target sweep completed: corrected Effect Core passed 6/6 and
specification examples passed 77/77. Only seven effect-diagnostic and five
effect-module predecessor expectations failed, each on unexpected acceptance
of a formerly forbidden live clause. Parent reviewed all five module fixtures:
the registration belongs to the selected Stop capture; specialization adds a
contained E clause; the residual-graph and caller-return variants contain their
C capture; and the declaration-only helper contains its A capture. These are
owned-closure positives, not outside-owner exceptions. Their source bodies and
distinct/coincident and before/after variants must remain, with linked runtime
checks where practical. The writer separately audits the seven diagnostic
fixtures before changing their expectations. Unrelated resource-escape
negatives remain unchanged.

Focused migration execution passed all 13 module tests through public linking
and evaluation, and 21 of 22 diagnostic tests. The unchanged
`capture-prefix-after.ash` fixture revealed a genuine source-to-Core boundary
failure: source checking succeeds but public independent validation rejects
resume node 42. This is not covered by the earlier raw-Core mutation witness.
The writer is tracing the resume and handler rows before choosing a correction;
the original fixture remains the failing end-to-end witness.

Exact instrumentation confirms resume node 42 has the closed empty row while
its actual owning handler 48 has `{D}`. The failure follows one-pass nested
clause replay, not source rejection or a validator defect. The writer is
extending the existing charged row replay to closure after discard equations
solve, retaining independent validation and checking finite propagation,
rollback and exact/one-short/fresh work. A high-reasoning reviewer is checking
those invariants read-only; no second capture analysis or raised limit is part
of this correction.

The original prefix-after source now passes public independent validation and
executes to Unit (`/tmp/ash-cleanup-step3-prefix-resume-closure-20260908.log`,
inspected by parent). The source-only builder closure uses actual handler/owner
identity, an entry-row snapshot and charged existing range equations. Its
convergence argument and multi-round budget/rollback witnesses remain under
review, including whether specialization can invalidate the lower-approximation
seed. This focused pass alone does not close the correction.

Review rejected the cached-seed argument: when two generic effect instances
coincide, exact handler removal can shrink a row, and a stale cached label can
self-support through Resume. The writer accepted that finding. The revised
closure starts derived Resume rows at bottom after identities are fixed, uses
provisional removal only during lower-approximation replay, and requires a
strict final sweep. A cached-label coincidence regression and genuine
missing-handler-member negative must accompany the exact/fresh rollback checks.
Neither provisional replay nor a focused pass weakens independent validation.

The stale-cache regression first failed with an extra self-supported effect,
confirming the review finding. Revised least-seed replay then passed 75 focused
top-level tests plus one small-stack subprocess: 23 library/Core checks,
11 abandonment, six interaction, 22 diagnostic and 13 module tests. Parent
inspected `/tmp/ash-cleanup-step3-replay-seed-green-20260908.log` and
`/tmp/ash-cleanup-step3-replay-source-green-20260908.log`. Coverage includes
multi-round exact/one-short/fresh rollback, delayed removal, strict missing-member
rejection, stale-cache clearing, both Core transforms, explicit open-row lacks
and the exercised opaque-guard companion. Independent bounded review then passed:
least-seed, tail/lacks, exact ownership, charging and whole-closure rollback have
no outstanding finding. Fresh full verification is running at
`/tmp/ash-cleanup-step3-full-verify-complete-20260908.log`. The two existing
architecture inventory equation paths were mechanically updated to the renamed
private replay helper; the full scan must authenticate that relocation.

The final gate exited 0: 2,545 top-level tests across 77 binaries plus eight
logged subprocess rechecks passed. Strict Clippy, all 32 architecture checks
(including the relocated inventory), formatting, build and warnings-denied
rustdoc passed without warnings or errors. Parent inspected the terminal log
and independently tallied its results. Final semantic/resource and bounded
correction reviews passed; all product/test/Cargo ownership returned to parent.
The complete product checkpoint now retains CLEAN-01 through CLEAN-11 evidence.
Transition artifact removal, unsigned local merge, merged verification and
clean worktree/branch removal remain the final lifecycle gates.
