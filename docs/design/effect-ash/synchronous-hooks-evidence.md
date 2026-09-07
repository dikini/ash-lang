# Synchronous hook implementation evidence

This informative report records partial implementation of accepted
[CP-0018](../../proposals/CP-0018-synchronous-typed-hooks.md), tracked by
[TASK-0028](../../tasks/TASK-0028-implement-synchronous-hooks.md). It does not
define language behavior or claim the complete hook contract is implemented.
The branch specification remains prospective until integration into `main`.

## Retained checkpoints

Unsigned checkpoint `bb618e8` retains primary syntax and projection for `hook`
and `register`. Unsigned checkpoint `e801edb` retains authenticated executable
roots. The registration proof increment retains structure and completion
checking after independent semantic and Rust/resource reviews and final parent
verification. Runtime ownership remains outstanding.
No integration merge, push or tag has occurred for this feature.

Both public Effect validators run registration proof before unconditionally
rejecting executable registration admission. Owning tests use a private,
test-only proof wrapper for transforms; it is not a production bypass. Positive
registration proof below is not evidence of runtime execution.

## Contract coverage

The case names below retain CP-0018's complete evidence matrix. A partial row is
not evidence for its outstanding requirements.

| Case | Evidence and outstanding work |
| --- | --- |
| HOOK-01: API and syntax | [Syntax tests](../../../tests/hooks_syntax.rs) cover primary positions, grouping, qualified/generic targets, source spans, malformed forms and both keyword collisions. [Typing tests](../../../tests/hooks_typing.rs) reject wrong names, multiple operations and `Convert<Int, Int>`, and check original argument kind spans and ordinary diagnostic precedence. Registration callback/body errors and conservative rows are covered; owning validation tests cover contextual identity lambdas, latent effects and ordinary polymorphic bindings. |
| HOOK-02: Identity and scope | [Runtime tests](../../../tests/hooks_runtime.rs) observe identity publication and unused roots. Typing tests pair existing open-tail lacks with ambiguity rejection and preserve ordinary handler missing-input rejection. Generic phantom instances distinguish equal and unequal specialization; [Core tests](../../../tests/hooks_core.rs) repeat facade and open-lacks helper cases after identity and folding transforms. Registration interactions remain outstanding. |
| HOOK-03: Ordered transformation | Generated forward–callback–resume order and the preceding initializer binding are independently checked. Runtime ordering, intermediate payloads, initializer timing and removal remain outstanding. |
| HOOK-04: Effects and handler placement | Root helper rows and enclosing resume scope are covered. Registration tests retain forwarded and latent requirements for unused scopes, reject missing initializer effects and prove open-lacks helpers through transforms. Runtime handler-placement observations remain outstanding. |
| HOOK-05: Nested publication and scoped changes | Outstanding: older-prefix visibility, temporary callback registrations and pending sequence preservation. |
| HOOK-06: Captured values and transformed dependencies | Root tests retain live resource-dependent function payloads and reject outward lending. Registration tests admit callback-added dependencies within the cell owner, reject escape and reject outward input before later erasure. [Module tests](../../../tests/effect_modules.rs) pair opaque/facade factory retention with escape; owning Core tests cover imported selected-evidence factories and both transforms. Actual linked callback substitution rejects an added escaping dependency. Runtime observations remain outstanding. |
| HOOK-07: Control and normal release | Generic root coincidence preserves pending resume obligations. Registration proof rejects unused-owner abandonment and skipped completion, admits initializer discard before acquisition and subscriber-local discard inside nested owners, and distinguishes consumed clause owners. Actual linked callback substitution rejects changed completion behavior. Same-site runtime activations and deregistration remain outstanding. |
| HOOK-08: Independent authority | Validator units reject root and registration API/target, binder, order, row and origin corruption through both transforms. Detached and duplicate registration owners reject. Linked same-typed callback changes independently reject unsafe completion or resource escape before the runtime gate. Registration execution after transforms remains outstanding. |
| HOOK-09: Resources and failure | Root and registration resolution, elaboration and proof have owning exact/one-short/fresh-retry tests. Deep partial state disposes on small stacks; the registration compiler pipeline has a 24-scope witness. Runtime capacity, captured ownership and activation failures remain outstanding. |
| HOOK-10: Migration and tools | Focused effect/resource predecessors and architecture checks pass at the root checkpoint. Complete hook specification updates, exact documented CLI output, full closing verification and Pure locality checks remain outstanding. |

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
product edits; it is not a substitute for the outstanding full closing gate.

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

Registration runtime, the complete HOOK-01 through HOOK-10 corpus, resulting
specification, full closing verification and local integration remain
outstanding. A synthetic signature-disposal failure encountered while preparing
one test was outside its intended boundary; it is not claimed fixed or used as
that test's RED evidence.
