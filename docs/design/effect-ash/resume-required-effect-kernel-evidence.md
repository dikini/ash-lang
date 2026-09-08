# Resume-Required Effect Kernel Evidence

This report maps the retained implementation evidence for Ash's first
resume-required effect kernel. It is informative, not normative. The
[Ash specification](../../../spec/README.md) alone defines the current
language on this integration branch; the result is not current on `main` until
separately approved integration. The historical transition was authorized by
CP-0013; this retained report does not depend on that temporary proposal or its
execution plan.

## Retained boundary

The implementation retains module-owned effect and operation identities,
identity-bearing open and closed computation rows, checked requests, exhaustive
ordered lexical handlers, and one non-escaping resume capability per clause.
Effect Core is one operation-family instantiation of the shared Core substrate.
The explicit evaluator moves an ordered frame suffix into a first-order captured
continuation and reinstalls it without a Rust closure or copied control.

Programs with no effect syntax retain the uninhabited Pure Core operation
family and the predecessor evaluator transitions. An imported but unused effect
declaration does not select Effect Core.

## Required evidence map

The following table maps the kernel obligations to the narrowest existing
named observations. Test names are exact.

| Kernel obligation | Retained observation |
| --- | --- |
| Grammar, precedence, recovery, and reservation | `recognizes_effect_reserved_words_without_stealing_identifier_boundaries` in [`tests/lexer.rs`](../../../tests/lexer.rs); all four tests in [`tests/effects_syntax.rs`](../../../tests/effects_syntax.rs) |
| Effect and operation identity, import, re-export, visibility, and distinct identity | `public_effect_identity_survives_facade_reexport`, `effect_namespace_privacy_and_diamond_routes_preserve_one_identity`, and `hidden_effect_signature_closure_survives_facade_and_diamond_routes` in [`tests/effect_modules.rs`](../../../tests/effect_modules.rs); `effect_and_operation_identities_are_stable_and_owner_scoped` and `closed_rows_are_unordered_idempotent_exact_instance_sets` in [`tests/effect_rows.rs`](../../../tests/effect_rows.rs) |
| Kind and argument admission | `local_and_imported_effect_rows_authenticate_effect_arity` in `tests/effect_modules.rs`; `row_inference_has_a_fixed_effect_row_kind` and `family_core_scheme_projection_preserves_pure_erasure_and_effect_rows` in [`src/elaborate.rs`](../../../src/elaborate.rs) |
| Row equality, substitution, union, lacks, exact removal, unrelated tails, and rendering | `closed_rows_are_unordered_idempotent_exact_instance_sets`, `substitution_reaches_exact_arguments_and_preserves_row_lacks`, `open_row_union_requires_an_existing_lacks_fact`, `union_retains_one_shared_tail_and_rejects_unrelated_tails`, `exact_removal_does_not_remove_another_instance_or_search_an_unknown_tail`, and `computation_rendering_distinguishes_latent_rows_and_canonicalizes_pure_functions` in `tests/effect_rows.rs` |
| Row unification, duplicate coalescing, generalization, and instantiation | `row_inference_unifies_exact_members_and_rejects_occurs`, `row_unification_comparisons_are_charged_exactly_and_retry_disjoint_width`, and `row_inference_generalizes_and_instantiates_without_entering_value_positions` in `src/elaborate.rs`; `open_global_relay_and_local_higher_order_function_generalize_effect_rows` in [`tests/effect_typing.rs`](../../../tests/effect_typing.rs) |
| Pure, closed, higher-order latent, branch union, open relay, and two-instance typing | `closed_handler_discharges_exact_effect_and_keeps_main_pure`, `strict_children_and_branches_union_rows_before_exact_discharge`, `open_global_relay_and_local_higher_order_function_generalize_effect_rows`, and `handlers_forward_other_instances_remove_exactly_and_reintroduce_direct_requests` in `tests/effect_typing.rs` |
| Operand/result typing, exhaustive coverage, forwarding, exact discharge, reintroduction, and closed entry | `handlers_forward_other_instances_remove_exactly_and_reintroduce_direct_requests` in `tests/effect_typing.rs`; `handler_coverage_patterns_and_exact_input_have_stable_diagnostics` and `annotation_and_open_union_failures_are_stable_and_poison_partial_elaboration` in [`tests/effect_diagnostics.rs`](../../../tests/effect_diagnostics.rs) |
| Resume exactly once, branch agreement, and non-escape | `resume_usage_accepts_exactly_once_in_every_match_branch` in `tests/effect_typing.rs`; `resume_usage_rejects_zero_double_branch_and_capture` and `resume_outside_a_handler_clause_is_rejected_by_resolution` in `tests/effect_diagnostics.rs` |
| Different-effect and same-effect dynamic order, forwarding, restoration, delegation, and clause return | `nested_forwarding_restores_intervening_handlers_in_original_order`, `nearest_delegation_and_sequential_requests_preserve_clause_control`, `clause_request_bypasses_captured_intervening_handler`, and `distinct_parameterized_instances_select_exact_handlers` in [`tests/effect_runtime.rs`](../../../tests/effect_runtime.rs) |
| Explicit Effect Core, row-bearing instantiation, independent forgery rejection, transforms, and Pure dialect exclusion | All four tests in [`tests/effect_core.rs`](../../../tests/effect_core.rs), including the open-row relay lowered through `TypeApplication` and two transform/revalidation passes; `effect_type_application_authenticates_complete_row_arguments` in [`src/core/validate.rs`](../../../src/core/validate.rs); `type_substitution_replaces_one_row_binder_with_complete_rows` in [`src/types.rs`](../../../src/types.rs); and `effect_dialect_adds_one_operation_family_without_changing_pure_families`, `pure_dialect_is_named_and_has_no_inhabited_operation_family`, and the `TypeApplicationNode.row_arguments` carrier entry in [`tests/architecture.rs`](../../../tests/architecture.rs) |
| Deep request, forwarding, and resume without host-stack recursion | `deep_forwarded_continuation_executes_on_a_small_host_stack` in `tests/effect_runtime.rs`; `captured_control_quota_is_exact_atomic_retryable_and_iteratively_disposed` in [`src/eval/machine.rs`](../../../src/eval/machine.rs) |
| Exact resource success, one-short atomic failure, retry, and iterative teardown | `effect_row_and_computation_clone_are_exact_atomic_and_retryable`, `row_algebra_owners_are_exact_atomic_and_retryable`, `nested_row_arguments_clone_and_substitute_on_a_small_stack`, and `charged_row_rebuild_failure_discards_staged_arguments_on_a_small_stack` in [`src/types.rs`](../../../src/types.rs); `source_effect_row_rebuild_is_exact_retryable_and_stack_safe` in [`src/resolve.rs`](../../../src/resolve.rs); `wide_handler_coverage_is_exact_atomic_and_retryable`, `deep_resume_usage_is_iterative_exact_and_retryable`, and `effect_core_selection_scan_is_exact_retryable_and_stack_safe` in [`src/elaborate.rs`](../../../src/elaborate.rs); `effect_clause_admission_is_exact_atomic_and_retryable` and `effect_row_type_application_admission_is_exact_atomic_and_retryable` in [`src/core/dialect.rs`](../../../src/core/dialect.rs); `wide_effect_handler_validation_is_exact_and_retryable` and `type_application_row_argument_scope_work_is_exact_atomic_and_retryable` in [`src/core/validate.rs`](../../../src/core/validate.rs); `effect_handler_rebuild_is_exact_retryable_and_deep_drop_safe` in [`src/core/transform.rs`](../../../src/core/transform.rs); and `captured_control_quota_is_exact_atomic_retryable_and_iteratively_disposed` plus `sequential_requests_reclaim_the_exact_effect_capture_quota` in [`src/eval/machine.rs`](../../../src/eval/machine.rs) |
| Source, module, and CLI observations | `handled_effect_prints_the_resumed_value_and_pure_entry_type` in [`tests/cli.rs`](../../../tests/cli.rs); `same_spelled_imported_effects_are_handled_independently` in [`tests/module_cli.rs`](../../../tests/module_cli.rs); `evaluates_a_handled_effect_through_effect_core` and `rejects_a_nonempty_entry_effect_row_before_core_lowering` in [`tests/module_entry.rs`](../../../tests/module_entry.rs); `written_duplicate_effect_row_has_exact_reason_code` in [`tests/effect_diagnostics.rs`](../../../tests/effect_diagnostics.rs); and `effect_examples_have_exact_observations_and_reasons` in [`tests/spec_examples.rs`](../../../tests/spec_examples.rs) |
| Predecessor Core, transform, evaluator, interface, module, resource, and corpus observations | The pre-existing cases remain in `tests/corpus.rs`; Pure Core and evaluator ownership stay closed through `pure_dialect_is_named_and_has_no_inhabited_operation_family`, `type_erasure_enters_each_explicit_operation_once_without_runtime_state`, and the exact 14-entry pure transition inventory in `src/eval/machine.rs`. The effect tests reuse the existing module, interface-evidence, Core transform, and explicit-machine paths rather than parallel owners. |

## Combined corpus closure

[`tests/fixtures/effects/valid/effect-kernel-combined.ash`](../../../tests/fixtures/effects/valid/effect-kernel-combined.ash)
is the one planned combined case. It contains:

- a polymorphic open-row `relay`;
- `Read<Int>` and `Read<Bool>` as two exact instances of one API;
- a `Read<Bool>` handler nested inside a `Read<Int>` handler, forcing the
  integer request to forward across the nonmatching inner boundary; and
- exactly one `resume` in each selected clause, after which the restored inner
  handler receives the Boolean request.

`every_valid_corpus_presentation_has_its_exact_library_and_cli_observation`
now checks the complete program through both retained entry paths. The library
observation is value `42` with type `Int`, and the exact CLI output is
`42 : Int` followed by a newline. The open row is retained as the complete row
argument of the shared `TypeApplication` carrier through admission,
transformation, independent validation, and erasure. The two exact instances
remain distinct, the integer request crosses and later regains the nested
Boolean handler boundary, and each selected clause resumes exactly once.

The normative source, typing, elaboration, and one-step runtime rules are in the
linked specification. This report records the implementation observations; it
does not claim or replace the independent reviews required before transition
cleanup or integration.
