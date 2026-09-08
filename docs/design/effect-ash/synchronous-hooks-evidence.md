# Synchronous hook implementation evidence

This informative report records the verified implementation of historical
`CP-0018`, tracked by historical `TASK-0028`. Both transition artifacts and the
task-owned plan are retained in product checkpoint `ad2b0d4`. This report does not
define language behavior. The complete hook contract passes its final reviews
and verification; local integration remains a separate lifecycle step.
The branch specification remains prospective until integration into `main`.

## Retained checkpoints

Unsigned checkpoint `bb618e8` retains primary syntax and projection for `hook`
and `register`. Unsigned checkpoint `e801edb` retains authenticated executable
roots. The registration proof increment retains structure and completion
checking after independent semantic and Rust/resource reviews and final parent
verification in unsigned checkpoint `07bb726e`. The final runtime, interaction
corpus and specification now pass independent reviews and full verification.
Unsigned product checkpoint `ad2b0d4` retains that complete implementation,
specification, tests, review and verification. The finished proposal, task and
execution plan are removed after that checkpoint; Git preserves them.
No integration merge, push or tag has occurred for this feature.

At `07bb726e`, both public Effect validators run registration proof before unconditionally
rejecting executable registration admission. Owning tests use a private,
test-only proof wrapper for transforms; it is not a production bypass. Positive
registration proof below is not evidence of runtime execution.

## Runtime findings

The runtime implementation removes the temporary public gates after adding a private,
non-Clone registration owner frame. Non-owning keys associate generated handler
and clause frames with that owner. Capture and resume move the owning frame;
normal return consumes it. This ownership invariant does not require a global
registry to detect an impossible copy of a private owning frame. Stale or
duplicated non-owning facts are checked at request and resume transitions.
Final runtime reviews and full verification pass.

Three unchanged witnesses identified corrections during this increment:

- Callback-environment preparation originally happened after capture. A failed
  extension left one frame instead of the original two. Preparation now
  precedes capture; the owning preflight test passes without consuming control
  or changing registration counters.
- An imported callback with latent row `{| R}` under a signature containing
  `{Adjust<Int> | R}` checked at source but failed independent Core validation.
  Generated application lowering omitted the already-authorized lacks fact.
  It now uses ordinary row qualification and explicit application emission,
  preserving the least row and the existing independent authority check. The
  unchanged imported callback test passes through both transforms.
- Direct internal discard of a generated registration clause initially
  returned success. The clause's existing registration association now rejects
  that transition before consuming its capture. The full gate reruns this
  witness and the distinct permitted subscriber-local discard case.

An additional resume association scan was removed by reusing the existing
clause lookup, preserving ordinary hook-free resume work. No callback variant
restriction, new effect-row authority or second evaluator was introduced.

Independent semantic review found a defensive gap: return and
resume must reject an extra active non-owning handler for the same activation
before changing owner state. The existing charged scan can require one active
handler at request selection and zero other active handlers at return/resume.
Both transitions independently returned success in the failing witnesses.
The shared scan now enforces those exact counts, and both unchanged witnesses
pass. No additional scan or registry was added. Semantic re-review and the
complete corrected regression gate pass.

Registration-specific generic coincidence controls now execute through both
transforms. Equal and unequal instances produce `42` and `1` with a
callback-added dependency's cell still live; the equal escaping result rejects.
Completion controls resume with `4` and `3`, while both discard variants reject
because both retain registration completion. No unequal escaping success or
summary-erasure precision is required. An older ordinary handler returns `30`
to the registration callback, which produces `31`; this complements the
publisher-side interception case. These controls and the complete corrected
gate and reviews pass.

## Contract coverage

The case names below retain CP-0018's complete evidence matrix.

| Case | Retained evidence |
| --- | --- |
| HOOK-01: API and syntax | [Syntax tests](../../../tests/hooks_syntax.rs) cover primary positions, grouping, qualified/generic targets, source spans, malformed forms and both keyword collisions. [Typing tests](../../../tests/hooks_typing.rs) reject wrong names, multiple operations and `Convert<Int, Int>`, and check original argument kind spans and ordinary diagnostic precedence. Registration callback/body errors and conservative rows are covered; owning validation tests cover contextual identity lambdas, latent effects and ordinary polymorphic bindings. |
| HOOK-02: Identity and scope | [Runtime tests](../../../tests/hooks_runtime.rs) observe identity publication, unused roots and nested-root isolation. Typing tests pair existing open-tail lacks with ambiguity rejection and preserve ordinary handler missing-input rejection. [Core tests](../../../tests/hooks_core.rs) execute facade/open-lacks helpers and equal/unequal generic registration cases through both transforms, including live dependencies and pending completion. |
| HOOK-03: Ordered transformation | `registrations_transform_in_registration_order` observes `8` and reversed `7`. Initializer-once and repeated-entry tests observe `5614`; inner removal observes `843`. Intermediate callback payloads and registration-site logging observe `48`. Generated forward–callback–resume order and the preceding initializer binding are independently checked. |
| HOOK-04: Effects and handler placement | Typing tests retain forwarded and latent requirements for unused scopes and reject missing initializer effects. Runtime tests distinguish outer from publisher-local logging, ordinary exact interception (`30`), and an older ordinary handler's forwarded result (`31`). Imported callback type/row contexts execute through both transforms; an unused effectful callback leaves the cell unchanged. |
| HOOK-05: Nested publication and scoped changes | Older-prefix nested publication observes `82`, without replaying pending callbacks. Temporary callback registration and nested-root isolation observe `410` and `310`. Callback copies and static-request closures remain ordinary after deregistration and observe the later chain (`46`). |
| HOOK-06: Captured values and transformed dependencies | Source and linked-Core tests admit callback-added dependencies within the cell owner, reject escape and reject outward input before later erasure. [Module tests](../../../tests/effect_modules.rs) pair opaque/facade factory retention with escape. Core tests execute opaque and selected-evidence factories and equal/unequal live-dependency cases through both transforms. Tuple payload transformation and projection observe `44` with the cell live; aggregate and projected-function escape reject, as does forwarding an original dependent tuple before later erasure. Actual same-typed linked callback substitution rejects an added escaping dependency. |
| HOOK-07: Control and normal release | Proof rejects unused-owner abandonment and skipped completion, admits initializer discard before acquisition and subscriber-local discard, and distinguishes consumed clause owners. Runtime tests observe same-site overlapping activations (`13`), outward callback capture/resume with cells (`281`), inner removal and release/reuse. Generic registration completion resumes with `4`/`3`; both outward discard variants reject. Linked callback substitution rejects changed completion behavior. |
| HOOK-08: Independent authority | Validator units reject root and registration API/target, binder, order, row and origin corruption through both transforms. Detached and duplicate owners reject. Actual linked same-typed callback changes reject unsafe completion or resource escape. Positive registration fixtures now use public validation and execute after transforms; no private admission bypass remains. |
| HOOK-09: Resources and failure | Compiler/proof tests retain exact/one-short/fresh-retry and small-stack evidence below. Machine tests cover live and captured capacity, release/reuse, fresh identities, acquisition and invocation preflight, stale/duplicate non-owning facts, separate chain/callback work, and 1,025 registrations with cells on a 256 KiB stack through success and repeated internal failure. Corrected full verification passes. |
| HOOK-10: Migration and tools | All eight specification/tool updates pass medium review and Markdown lint. [The exact CLI test](../../../tests/spec_examples.rs) observes `8 : Int\n` with empty stderr and checks the documented source. All 76 documentation-example tests pass, as do the full predecessor/Pure-locality gate and final semantic and Rust/resource reviews. |

## Owning resource evidence

The owning tests retain measured work rather than an estimated allowance:

- `hook_identity_retention_is_exact_and_disposes_failed_deep_inputs` in
  [resolution](../../../src/resolve.rs) checks generated identity retention.
- `hook_body_and_identity_elaboration_are_exact_and_fresh_retryable` in
  [elaboration](../../../src/elaborate.rs) checks all shorter allowances with
  two phantom target arguments and a tuple.
- `hook_root_validation_is_exact_one_short_and_retryable` in
  [Core validation](../../../src/core/validate.rs) measures the root handler
  check, rejects one-short work and repeats two fresh exact allowances.
- `nested_hook_recompute_owns_partial_target_clones` in
  [Effect Core](../../../src/core/effect.rs) puts a 32,000-node left-associated
  application spine before a second phantom argument. Its failure cutoff is
  measured prefix work plus one extra range slot, one hook-node charge, two
  argument slots and the complete first clone. The unchanged cutoff originally
  overflowed during partial-clone disposal; it now reports exhaustion and
  restores retained rows. Separate full-work calibration checks one-short
  rollback and two fresh exact retries on a 256 KiB child stack.

The safe target clone charges argument slots before cloning, retains partial
arguments in iterative owners, then charges and reserves final argument slots
before transferring ownership. Nested roots use this path without changing
ordinary-handler work accounting.

`nested_root_pipeline_and_disposal_fit_a_small_stack` checks 24 roots on a fresh
256 KiB thread through direct loading, resolution, module checking, linking,
validation, evaluation and disposal. This follows the resource predecessor's
helper pipeline. It does not establish the same bound for the full `run_path`
wrapper: the matched resource control also overflowed through that wrapper.
No predecessor depth or resource ceiling was relaxed.

Registration resource tests add:

- `registration_retention_is_exact_and_disposes_failed_deep_inputs` in
  [resolution](../../../src/resolve.rs), including 32,000-node inputs.
- `registration_body_callback_and_owner_elaboration_are_exact_and_fresh_retryable`
  in [elaboration](../../../src/elaborate.rs), covering every insufficient
  allowance and two fresh exact retries with an anonymous callback.
- `registration_capture_work_is_exact_one_short_and_retryable` in
  [Core validation](../../../src/core/validate.rs), measuring the actual finite
  proof rather than assuming a fixed allowance.
- Three 4,096-depth/256-KiB failure witnesses in elaboration:
  `registration_contextual_function_disposes_deep_payload_when_provenance_budget_fails`,
  `registration_callback_check_disposes_first_deep_clone_when_second_clone_fails`,
  and `registration_lowering_disposes_deep_result_when_resume_row_budget_fails`.
  Each retained failure originally overflowed during recursive type disposal.
  Existing iterative owners now retain partial types until transfer.

The lowering witness uses the actual lowering function and a synthetic deep
intermediate body. Its unbounded control rejects Core admission after 16,439
elaborator work units; 16,438 units fail at the preceding resume-row clone.
It never constructs a successful invalid Core program. This one direct lowering
RED/GREEN, the same inspected guard at five fallible windows, exhaustive shallow
budget tests and existing deep owner-disposal evidence establish the shared
ownership correction. It is not five separate deep reproductions. Structural
depth limits do not bound all host ownership depth: type-application left spines
can remain deeply owned after admission.

`registration_pipeline_and_disposal_fit_a_small_stack` checks 24 registrations
and an outer root through direct loading, resolution, checking, linking and
independent proof on 256 KiB. Its original helper overflowed, as did a matched
root-only helper. Aligning with the accepted direct root harness retains source,
depth, stack and compiler phases; this is not an unchanged-helper success or a
runtime test. A later contextual-typing correction regressed this unchanged
witness. Extracting ordinary binding scheduling verbatim reduced the measured
shared frame from 109,152 to 106,944 bytes and restored both root and registration
witnesses without further harness or limit changes.

## Runtime resource evidence

Owning [machine tests](../../../src/eval/machine.rs) measure registration work
separately from the compiler ledgers above. Acquisition charges
`3 + environment.len()` before retaining two frames and their callback relation
and looking up the callback. Each owner-association scan charges the active
frame count before traversal. Generated resume additionally charges its captured
frame count for association checking; restoration preflight charges that count
when registrations are live. Ordinary request search and callback evaluation
retain their existing work. These are charged traversal bounds, not a claim
that every publication has one fixed total cost.

`registration_publication_work_is_exact_one_short_and_fresh_retryable` measures
the complete evaluator ledger for the two-registration program, rejects one
less and repeats two fresh exact runs. Acquisition separately has the same
boundary controls. `registration_chain_steps_are_separate_from_ordinary_callback_work`
uses chains of 1, 2 and 4 registrations with callbacks containing either one or
four primitives. A chain of N has N acquisitions, N+1 requests, selections and
resumes including the root, and N times the callback's primitive count.

Capacity tests lower the owning machine's limit to one or two entries. They
distinguish active and captured owners, reject one-short capacity, repeat exact
runs and reuse released capacity with fresh keys. Registration capacity is
separate from cell capacity; both default to the existing representable-frame
bound. Counter overflow, missing binding and failed work preparation publish
no partial acquisition. Invocation preflight preserves the original frames,
capture count and registration state on failure.

`deep_registration_callbacks_capture_cells_and_dispose_failure_on_a_small_stack`
compiles a recursive source fixture before entering a fresh 256 KiB thread.
Evaluation on that thread acquires 1,025 registrations and cells, invokes each
callback once, and returns the sum of depths. Two fresh bounded runs fail at the
first callback's `Pause` request and dispose pending control, owners and
environments on the same small stack. This is runtime success and failure
evidence, not compilation of that fixture on a small stack. Separate compiler
witnesses retain their stated 24-scope bounds.

Actual stale and duplicate non-owning handler transitions are tested without
copying the private owning frame. Independent Rust review additionally found
that clause return must compare retained clause associations with its pending
count before mutation. Its unchanged witness first returned success, then
passed after adding that comparison to the existing scan. The check accounts
for the popped clause at return, preserves state on rejection and permits the
original clause and owner to complete afterward. Source re-review confirms
the invariant, and the corrected full gate passes.

## Review and verification

Independent high-reasoning semantic review found diagnostic ordering and
identity-pattern origin gaps. Both original failing witnesses pass after
correction. Rust/resource review closed the remaining nested-root partial-clone
failure after inspecting its RED/GREEN and rollback evidence. Both reviews pass
for the root checkpoint only.

The final parent gate at `e801edb` passed 1,111 library tests and 176 focused
hook/effect/resource integration tests, formatting and strict Clippy. All 32
architecture tests passed before the final root-only clone-call correction;
the actual-field inventory was repeated successfully afterward. Markdown lint
and diff checks passed. The full baseline `cargo xtask verify` passed before
product edits; the final closing gate is recorded separately below.

Registration semantic review corrected anonymous callback generalization and
added an actual linked dependency-rejection witness. The linked completion test
also exposed missing value demand for enclosing linked bindings; demanding the
existing root port restores actual callback discovery. Rust/resource review
closed five raw-type ownership windows after the lowering failure above.
Both reviews now pass for the proof checkpoint. Writer verification passes
1,131 library tests, 229 focused integration tests, formatting and full strict
Clippy. All 32 architecture checks passed before the final five local guards and
private lowering test; those changes add no carriers. The final parent repeat
passes 1,131 library tests, 229 focused integration tests, all 32 architecture
checks, formatting and full strict Clippy on the corrected snapshot. The
independent medium evidence-document audit also passes.

An intermediate runtime run passed 34 registration-focused library tests, then the
unfiltered 11 Core, 15 runtime, 23 typing and 76 documentation-example tests,
including exact CLI output. High semantic re-review passes. Strict Clippy and
formatting pass after a conditional-only style correction. Rust/resource review
closed the consumed-clause multiplicity finding above. Its unchanged regression
and aggregate controls pass in the corrected targeted run: 35 library, six Core
and 13 typing tests.

The final September 8 parent `CARGO_INCREMENTAL=0 cargo xtask verify` completed
all phases successfully: formatting, locked metadata/build, strict Clippy,
2,470 workspace tests and warnings-denied rustdoc. The test total comprises
1,142 library, 10 executable, 1,317 integration and one xtask test; child-process
reruns are not counted twice. The integration total includes all 32 architecture
checks (309.98 seconds), 12 hook Core, 15 hook runtime, seven hook syntax,
25 hook typing and 76 documentation-example tests. The original tool session
receipt was lost during context truncation; the successful completed phase log
and terminated process were inspected. Merged-checkout verification will retain
a separate exit receipt.

Final independent high semantic and Rust/resource audits pass without remaining
findings. The medium documentation audit verifies all eight affected files,
43 local links/anchors, formal notation, exact CLI coverage and the resource
claims above. Markdown lint and diff checks pass. No predecessor test, resource
ceiling, independent validation boundary or Pure inventory was weakened.

The representation remains one private registration owner plus ordinary
handlers and callable values. Future cleanup must define admitted exits and
failure ownership; hooks add no implicit cleanup, registry, general ownership
framework or second evaluator. Proofs, existentials, async hooks and foreign
providers remain outside this checkpoint.

A synthetic signature-disposal failure encountered while preparing
one test was outside its intended boundary; it is not claimed fixed or used as
that test's RED evidence.
