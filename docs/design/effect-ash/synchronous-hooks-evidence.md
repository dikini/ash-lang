# Synchronous hook implementation evidence

This informative report records partial implementation of accepted
[CP-0018](../../proposals/CP-0018-synchronous-typed-hooks.md), tracked by
[TASK-0028](../../tasks/TASK-0028-implement-synchronous-hooks.md). It does not
define language behavior or claim the complete hook contract is implemented.
The branch specification remains prospective until integration into `main`.

## Retained checkpoints

Unsigned checkpoint `bb618e8` retains primary syntax and projection for `hook`
and `register`. Unsigned checkpoint `e801edb` retains authenticated executable
roots. Registration structure, completion proof and runtime ownership are still
in progress. No integration merge, push or tag has occurred for this feature.

## Contract coverage

The case names below retain CP-0018's complete evidence matrix. A partial row is
not evidence for its outstanding registration requirements.

| Case | Retained evidence and outstanding work |
| --- | --- |
| HOOK-01: API and syntax | [Syntax tests](../../../tests/hooks_syntax.rs) cover primary positions, grouping, qualified/generic targets, source spans, malformed forms and both keyword collisions. [Typing tests](../../../tests/hooks_typing.rs) reject wrong names, multiple operations and `Convert<Int, Int>`, and check original argument kind spans and ordinary diagnostic precedence. Registration target/type checking remains outstanding. |
| HOOK-02: Identity and scope | [Runtime tests](../../../tests/hooks_runtime.rs) observe identity publication and unused roots. Typing tests pair existing open-tail lacks with ambiguity rejection and preserve ordinary handler missing-input rejection. Generic phantom instances distinguish equal and unequal specialization; [Core tests](../../../tests/hooks_core.rs) repeat facade and open-lacks helper cases after identity and folding transforms. Registration interactions remain outstanding. |
| HOOK-03: Ordered transformation | Outstanding: registrations, intermediate payloads, initializer timing and removal. Root identity alone does not prove ordering. |
| HOOK-04: Effects and handler placement | Root helper rows and enclosing resume scope are covered. Registration-site callback handling and conservative unused callback effects remain outstanding. |
| HOOK-05: Nested publication and scoped changes | Outstanding: older-prefix visibility, temporary callback registrations and pending sequence preservation. |
| HOOK-06: Captured values and transformed dependencies | Root tests retain live resource-dependent function payloads, reject temporary outward lending, and distinguish generic coincidence from interception. Core tests repeat live payloads after both transforms. Dependencies added or erased by callbacks and imported callback factories remain outstanding. |
| HOOK-07: Control and normal release | Generic root coincidence preserves pending resume obligations and rejects unsafe discard when the outer handler is reached. Registration completion, same-site activations and deregistration remain outstanding. |
| HOOK-08: Independent authority | Validator units reject root API, target, clause, origin and row corruption before and after both transforms. Registration owner/callback/forwarding relationships and independent completion proof remain outstanding. |
| HOOK-09: Resources and failure | Root resolution, elaboration, validation and nested-row recomputation have owning exact/one-short/fresh-retry tests. Deep partial clones dispose on a small stack and failed recomputation restores rows. Registration capacity, captured ownership and activation failures remain outstanding. |
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

Registration runtime, the complete HOOK-01 through HOOK-10 corpus, resulting
specification, complete reviews and local integration are not yet verified.
