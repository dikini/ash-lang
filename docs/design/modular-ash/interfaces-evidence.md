# Interfaces and Implementations Integration Evidence

This report records implementation evidence for Modular Ash's interfaces and
implementations increment. It is informative, not normative. The
[normative specification](../../../spec/README.md) owns the current language.
The retained [interface design note](../DN-0023-interfaces-and-implementations.md),
[dialect-milestone note](../DN-0020-ash-dialect-milestones.md), and
[passive-module evidence](evidence.md) explain the design pressure and the
module boundary on which this increment depends.

## Scope and checkpoints

The comparison baseline is commit
`ca7932877df3553cbb2325c7a73a0b38812b5db8`, which accepts the interface
transition.
The original increment's normative checkpoint is unsigned commit
`f783271dab81db382e0fdcc1c8a1fe4abb12cea3`. The principal checkpoints from the
accepted transition through the current corrective product work are:

- `ff2ea36`, which authorizes the interface implementation work;
- `3d53619`, which admits interface and implementation syntax;
- `898afec`, which resolves interface identities and constraints;
- `45790f7` and `f3bbc3a`, which check interface declarations and
  implementation headers;
- `f4d89e6`, which publishes checked body-free interface and implementation
  summaries;
- `3cd2618`, which selects structural checked evidence;
- `40c4682`, which retains exact occurrence and import provenance;
- `2c2fd28`, which independently validates linked interface evidence before
  Core synthesis;
- `1280299`, which lowers validated evidence to the existing Core dialect;
- `3c78cfd`, which completes generic prerequisite evidence;
- `1dc03c2`, which retains the interface integration corpus and bounded
  unspecialized trace;
- `6f36d77`, which closes diagnostic evidence;
- `a93bdbb`, which establishes graph-wide resource boundaries;
- `301de2a`, which historically admits an interface method when an arrow occurs
  anywhere inside its type;
- `f783271`, which replaces the normative interface specification;
- `364c736`, whose corrective product work narrows the former rule to require
  `Function` as the method type's outermost constructor;
- `18c04fd`, which rebaselines the affected resource evidence and makes rejected
  resolved interface payloads safe to destroy iteratively; and
- `089c54e`, which updates the normative specification and retained evidence for
  the outer-`Function` correction;
- `5210beb`, which corrects checkpoint scope and task progress; and
- `ee998a0`, which reconciles the remaining historical and current checkpoint
  provenance.

All named checkpoints are unsigned. The final reviewed product checkpoint is
`ee998a05e9783972dc9952024fce2720b5d41449`. Current `main` at `8f4de9a` is an
incorporated ancestor, but the product remains unmerged on
`feature/modular-ash`. The review and verification section below records that
product boundary. This report and transition cleanup do not move it.

## Causal semantic model

Parsing and projection retain one-parameter interfaces, ordered methods,
ordered global requirements, implementation heads, ordered prerequisites, and
implementation equations. Resolution replaces their source spellings with
module-qualified identities. It allocates an occurrence-local empty evidence
slot for each resolved constrained-global or interface-method occurrence and
retains the exact complete-import declaration or targeted selector used by an
imported occurrence.

Checking authenticates top-level function interface shapes, constrained
schemes, implementation ownership, prerequisite decrease,
effective-environment non-overlap, membership, method types, and bodies.
Substituting an implementation or requirement argument preserves each method's
outer `Function`, so implementation equations and flattened evidence slots
remain callable. Evidence selection then resolves each rigid obligation from
lexical abstract requirements, the exact current implementation, or concrete
available implementations, in that order. The owning obligation-closure
boundary fills each structural slot exactly once. This includes an eligible
unannotated anonymous-function initializer before local generalization, as well
as constrained globals and implementation methods. Checked definitions retain
the filled occurrence with their checked group through linking; no later stage
joins spans or repeats selection.

A module publishes a body-free immutable summary only after all its declarations
and bodies check. The summary preserves public interface and method facts,
public implementation facts, stable identities, checked schemes, ordered
prerequisites and method mappings, provenance, and the hidden nominal or
interface closure needed to authenticate those facts. It does not transport a
body, private name environment, private implementation, or an implementation
imported from another module. A dependent therefore sees public implementations
from its direct dependencies only, regardless of complete versus targeted
import syntax.

Linking combines complete checked definitions and registries from every module.
Linked interface-evidence validation authenticates the retained identities,
occurrence-module availability, exact direct import edge, substitutions,
prerequisite trees and termination, method order and mappings, scope, types,
and provenance before Core synthesis. It does not infer, select, or repair
evidence. Core synthesis then flattens every requirement or prerequisite in
declaration order and, within it, every interface method in declaration order.
At an occurrence, generated type applications precede evidence applications,
which precede source value arguments. The existing Core validator runs after
this synthesis.

Abstract evidence lowers to a lexical evidence binder. Concrete evidence lowers
to the selected implementation-method binder. Generic concrete evidence first
type-applies the recorded substitution and then supplies recursively lowered
prerequisite terms. Implementation-method binders join the defining module's
existing recursive group, so recursion, mutual recursion, global-to-method
calls, and method-to-global calls use ordinary lexical recursion.

## Stable identity, summaries, and availability

The semantic identity families are deliberately distinct:

- `InterfaceId` combines a defining `ModuleId` and source declaration ordinal;
- `MethodId` combines its `InterfaceId` and method declaration ordinal;
- `ImplId` combines a defining `ModuleId` and source declaration ordinal;
- `ImplMethodId` combines its `ImplId` and exact `MethodId`;
- `RequirementId` combines a global `BinderId` or `ImplId` owner with a
  requirement declaration ordinal; and
- each implementation method also has a hidden defining-module `BinderId` used
  by ordinary Core variables and recursive binding.

Aliases, targeted names, complete-import qualification, and alternate graph
routes do not change these identities. Alternate direct routes deduplicate the
same `ImplId`; they do not create an overlap with itself. A public
implementation is available in its defining module and in a module with an
authenticated direct dependency edge to its summary. It is not re-exported
through an intermediary.

Hidden summary closure preserves identity without granting source access. A
public constrained global or public implementation may use a public interface
defined by a direct dependency. Its checked summary retains that foreign public
interface's parameter and method shape to authenticate the public fact, but it
does not re-export the interface or create a source binding for it. A private
interface may constrain a private global declared in its defining module, but
it can never occur in a public constrained global. Separately, a public
implementation may retain a private nominal head identity while its private
spelling and constructors remain unavailable to an importer. An opaque public
type remains nameable, but its constructors and representation remain
unavailable in an external implementation body. These carriers authenticate
composition without turning a checked summary into a source module signature.

## Structural evidence and validation

The structural selection is part of each checked resolved occurrence, not a
side table keyed by source span. Empty slot clones have independent one-shot
cells; clones of a filled slot share the same immutable flat plan. The plan
records an abstract requirement identity or a concrete implementation identity,
its ordered type substitution, its ordered prerequisite subplans, and its
ordered implementation-method identities. Checked definitions and method groups
own those occurrences across the checked-module and linked-program transitions.

The independent validator rejects a linked program before Core synthesis when
any retained evidence fact is forged or inconsistent. Its checks cover:

- source declaration ordinals and distinct identity families;
- occurrence-module availability, public/private status, and the exact direct
  dependency route admitting an imported implementation;
- selected goal and rigid implementation-head substitution;
- prerequisite count, order, tree ownership, proper decrease, and absence of
  shared or cyclic corruption;
- interface-method count and order, `ImplMethodId` mapping, and hidden binder
  uniqueness;
- abstract requirement owner and argument;
- linked global and implementation-method schemes, lexical type scope, nominal
  arity, and absence of inference or unbound `forall`; and
- source and import provenance for the selected occurrence and fact.

Validation consumes the recorded plan. It neither consults source spelling to
reselect evidence nor treats an import span as an implementation identity.
Interface, implementation, method, and requirement identities are released
only after this validation has authorized ordinary Core synthesis.

## Core inventory and unspecialized execution

The closed pure Core inventory is:

- `PureExprKind`: `Value`, `Variable`, and `Computation`;
- `PureValue`: `Integer`, `Boolean`, `Unit`, `Function`, and `Constructor`;
- `PureComputation`: `Bind`, `RecursiveBind`, `Apply`, `Primitive`, `Tuple`,
  `Match`, `TypeAbstraction`, and `TypeApplication`.

The runtime `Value` inventory is `Integer`, `Boolean`, `Unit`, `Function`,
`ConstructorFunction`, `Location`, and `Data`. Extraction of these declarations
from `src/core/dialect.rs` and `src/eval/value.rs` produces no inventory diff
between `ca79328` and `f783271`. The identifier-level guard
`tests/architecture.rs::core_and_evaluator_keep_interface_evidence_outside_their_closed_inventories`
additionally scans every Core and evaluator Rust source.

Generated evidence therefore uses ordinary lexical functions and existing
evaluation transitions. `TypeApplication` erases the ordinary Core type
application formed from the recorded substitution; the evaluator does not
receive or inspect that substitution. `RecursiveBind` materializes the same
function closures used by source recursion. `Apply` performs existing strict
function and argument evaluation and beta application. There is no runtime
interface or dictionary value, interface Core node, implementation registry,
interface lookup, method dispatch, registration, discovery, or interface
failure mode.

The bounded test trace in
`tests/interfaces.rs::generic_prerequisite_evidence_has_a_bounded_unspecialized_evaluation_trace`
uses `Read<Int>` and `Read<Wrap<A>> where Read<A>` for `read(Wrap(42))`. The
generated Core enters the source application, evidence application, type
application, generic implementation-method variable occurrence, and ground
prerequisite implementation-method variable occurrence in that order. The
prerequisite occurrence is entered before the source argument. The result is
`42`, the node-entry trace contains at most 32 events, and the machine uses at
most six frames. This is an unspecialized test trace over existing evaluator
rules, not a new evaluation rule or a specialization claim.

## Required evidence

The required evidence for the accepted transition and corrective work is
retained by the exact targets and named witnesses below. A target can contain
additional boundary cases beyond the ones named here.

### Lexing, parsing, projection, recovery, and malformed forms

- [`tests/lexer.rs`](../../../tests/lexer.rs):
  `tests/lexer.rs::recognizes_interface_reserved_words_without_stealing_identifier_boundaries`.
- [`tests/interfaces_syntax.rs`](../../../tests/interfaces_syntax.rs):
  `tests/interfaces_syntax.rs::projects_ordered_requirements_on_both_global_presentations`,
  `tests/interfaces_syntax.rs::projects_generic_impl_prerequisites_and_flat_method_equations`,
  `tests/interfaces_syntax.rs::malformed_interface_and_impl_heads_retain_exact_expected_forms`,
  `tests/interfaces_syntax.rs::malformed_interface_method_recovers_at_its_logical_line`,
  `tests/interfaces_syntax.rs::interface_method_body_is_rejected_at_its_equal_and_recovers`,
  and `tests/interfaces_syntax.rs::preserves_interface_method_source_order`.

### Stable identities, namespaces, imports, aliases, routes, and diamonds

- [`tests/resolution.rs`](../../../tests/resolution.rs):
  `tests/resolution.rs::resolves_local_interface_and_method_identities`,
  `tests/resolution.rs::derives_impl_method_identity_from_impl_and_interface_method`,
  and
  `tests/resolution.rs::resolved_constraint_occurrences_start_with_owned_empty_evidence_slots`.
- [`tests/interface_modules.rs`](../../../tests/interface_modules.rs):
  `tests/interface_modules.rs::qualified_public_interface_and_method_keep_their_defining_identities`,
  `tests/interface_modules.rs::targeted_same_spelled_interface_and_constructor_bind_distinct_namespaces`,
  and
  `tests/interface_modules.rs::alternate_direct_routes_to_one_impl_identity_do_not_self_overlap`.
- [`tests/interface_identity_diamond.rs`](../../../tests/interface_identity_diamond.rs):
  `tests/interface_identity_diamond.rs::preserves_all_interface_identity_families_through_dependency_diamond`.

### Summary atomicity, hidden closure, direct availability, and no re-export

- [`tests/implementations.rs`](../../../tests/implementations.rs):
  `tests/implementations.rs::failed_public_impl_stages_never_produce_a_checked_summary`.
- [`tests/module_elaboration.rs`](../../../tests/module_elaboration.rs):
  `tests/module_elaboration.rs::failed_module_body_never_publishes_an_export_summary`.
- [`tests/interface_modules.rs`](../../../tests/interface_modules.rs):
  `tests/interface_modules.rs::hidden_interface_metadata_in_a_constrained_summary_is_not_reexported`,
  `tests/interface_modules.rs::public_impl_fact_is_available_on_a_targeted_direct_import_edge`,
  `tests/interface_modules.rs::private_impl_fact_remains_local_to_its_defining_module`,
  `tests/interface_modules.rs::public_impl_retains_its_private_head_identity_as_hidden_metadata`,
  and
  `tests/interface_modules.rs::public_impls_are_not_reexported_through_an_intermediary`.
- [`tests/interface_generic_summary.rs`](../../../tests/interface_generic_summary.rs):
  `tests/interface_generic_summary.rs::generic_checked_summary_binds_every_retained_parameter_occurrence`.

### Interface exposure, method shape, and entry boundaries

- [`tests/interface_modules.rs`](../../../tests/interface_modules.rs):
  `tests/interface_modules.rs::private_interface_and_method_are_not_qualified_import_bindings`
  and `tests/interface_modules.rs::private_method_is_not_a_qualified_import_binding`.
- [`tests/interfaces.rs`](../../../tests/interfaces.rs):
  `tests/interfaces.rs::rejects_public_global_requirement_on_private_interface`,
  `tests/interfaces.rs::accepts_private_global_requirement_on_private_interface`,
  `tests/interfaces.rs::rejects_interface_method_without_function_arrow`,
  `tests/interfaces.rs::rejects_interface_method_with_only_nested_function_arrow`,
  `tests/interfaces.rs::rejects_invalid_parameter_before_nested_function_shape`,
  `tests/interfaces.rs::accepts_top_level_function_with_nested_function_domain`,
  `tests/interfaces.rs::accepts_top_level_function_with_function_valued_codomain`,
  and
  `tests/interfaces.rs::top_level_function_with_nested_function_domain_completes_the_pipeline`.
- [`tests/implementations.rs`](../../../tests/implementations.rs):
  `tests/implementations.rs::rejects_public_impl_for_private_interface`,
  `tests/implementations.rs::rejects_public_impl_with_private_prerequisite`,
  and
  `tests/implementations.rs::rejects_invalid_interface_method_shape_before_impl_equation_arity`.
- [`src/elaborate.rs`](../../../src/elaborate.rs):
  `src/elaborate.rs::tests::invalid_outer_method_shape_has_an_exact_stack_safe_constraint_boundary`.
- [`tests/module_entry.rs`](../../../tests/module_entry.rs):
  `tests/module_entry.rs::rejects_a_constrained_main_before_lowering_entry_evidence`
  and
  `tests/module_entry.rs::existing_entry_shape_failures_precede_main_constrained`.

### Implementation ownership, overlap, route deduplication, and authentication

- [`tests/implementations.rs`](../../../tests/implementations.rs):
  `tests/implementations.rs::accepts_impl_for_local_interface`,
  `tests/implementations.rs::accepts_impl_for_local_outer_nominal`,
  `tests/implementations.rs::rejects_bare_type_variable_impl_head`,
  `tests/implementations.rs::rejects_identity_equal_local_implementation_heads`,
  and
  `tests/implementations.rs::rejects_generic_local_overlap_after_pair_local_freshening`.
- [`tests/interface_modules.rs`](../../../tests/interface_modules.rs):
  `tests/interface_modules.rs::rejects_foreign_interface_and_foreign_nominal_impl_as_orphan`,
  `tests/interface_modules.rs::rejects_primitive_impl_for_foreign_interface_as_orphan`,
  and
  `tests/interface_modules.rs::alternate_direct_routes_to_one_impl_identity_do_not_self_overlap`.
- [`src/elaborate.rs`](../../../src/elaborate.rs):
  `src/elaborate.rs::tests::imported_overlap_uses_retained_route_order_and_exact_budget`.

### Prerequisite termination, rigid selection, abstract priority, and failures

- [`tests/implementations.rs`](../../../tests/implementations.rs):
  `tests/implementations.rs::accepts_strict_subterm_prerequisite`,
  `tests/implementations.rs::rejects_expanding_prerequisite`, and
  `tests/implementations.rs::accepts_ground_prerequisite_without_subterm_decrease`.
- [`tests/interface_selection.rs`](../../../tests/interface_selection.rs):
  `tests/interface_selection.rs::constrained_method_selects_its_exact_abstract_requirement_before_a_matching_impl`,
  `tests/interface_selection.rs::absent_candidate_reports_constraint_unsatisfied`,
  `tests/interface_selection.rs::undetermined_obligation_reports_constraint_ambiguous_without_type_guessing`,
  and
  `tests/interface_selection.rs::rejects_public_global_obligation_instead_of_inferring_exported_requirement`.
- [`tests/interfaces.rs`](../../../tests/interfaces.rs):
  `tests/interfaces.rs::ground_cross_interface_prerequisite_cycle_has_the_exact_reason`.

### Method membership, typing, and recursive-group interactions

- [`tests/implementations.rs`](../../../tests/implementations.rs):
  `tests/implementations.rs::checked_membership_uses_interface_order_and_authenticates_source_groups`,
  `tests/implementations.rs::rejects_missing_impl_method`,
  `tests/implementations.rs::rejects_duplicate_impl_method_group`,
  `tests/implementations.rs::rejects_extra_impl_method`,
  `tests/implementations.rs::checks_impl_method_body_against_the_substituted_interface_signature`,
  and `tests/implementations.rs::rejects_wrong_impl_method_result_type`.
- [`tests/recursion.rs`](../../../tests/recursion.rs):
  `tests/recursion.rs::implementation_method_recurses_through_current_evidence`,
  `tests/recursion.rs::implementation_methods_share_mutual_recursive_scope`,
  `tests/recursion.rs::earlier_global_and_later_implementation_method_share_recursive_scope`,
  and
  `tests/recursion.rs::earlier_implementation_method_and_later_global_share_recursive_scope`.

### Constrained exports and abstract, concrete, generic, and higher-order evidence

- [`tests/interfaces.rs`](../../../tests/interfaces.rs):
  `tests/interfaces.rs::cross_module_constraint_lowers_to_method_evidence`,
  `tests/interfaces.rs::generic_option_impl_constructs_prerequisite_evidence`,
  `tests/interfaces.rs::generic_two_prerequisite_slots_preserve_declaration_order`,
  and
  `tests/interfaces.rs::generic_exact_current_self_carries_abstract_prerequisite_evidence`.
- [`tests/interface_corpus.rs`](../../../tests/interface_corpus.rs):
  `tests/interface_corpus.rs::higher_order_abstract_evidence_observes_true` and
  `tests/interface_corpus.rs::equational_and_operational_constraints_agree`.

### Hidden and opaque carrier implementations

- [`tests/interface_corpus.rs`](../../../tests/interface_corpus.rs):
  `tests/interface_corpus.rs::hidden_carrier_composes_to_forty_two` and
  `tests/interface_corpus.rs::opaque_carrier_uses_public_operations`.
- [`tests/interface_modules.rs`](../../../tests/interface_modules.rs):
  `tests/interface_modules.rs::private_impl_head_spelling_and_constructor_remain_unavailable`
  and
  `tests/interface_modules.rs::rejects_external_opaque_constructor_and_pattern_in_impl_body`.

### Structural occurrence evidence survives checking and is consumed once

- [`tests/interface_selection.rs`](../../../tests/interface_selection.rs):
  `tests/interface_selection.rs::constrained_global_occurrence_retains_one_abstract_selection_per_requirement_in_source_order`,
  `tests/interface_selection.rs::concrete_candidate_retains_impl_substitution_prerequisite_and_ordered_method_identity`,
  and
  `tests/interface_selection.rs::link_modules_retains_the_checked_occurrences_evidence_selection`.
- [`tests/interface_corpus.rs`](../../../tests/interface_corpus.rs):
  `tests/interface_corpus.rs::one_method_occurrence_does_not_retain_unused_same_typed_evidence`.
- [`src/evidence.rs`](../../../src/evidence.rs):
  `src/evidence.rs::tests::closure_zonks_then_fills_the_exact_structural_slot`.

### Pre-Core validation rejects corrupted linked evidence

- [`tests/interface_validation.rs`](../../../tests/interface_validation.rs):
  `tests/interface_validation.rs::validates_cross_module_concrete_selection_before_core`.
- [`src/evidence_validation.rs`](../../../src/evidence_validation.rs):
  `src/evidence_validation.rs::tests::rejects_wrong_generic_substitution_and_prerequisite_argument`,
  `src/evidence_validation.rs::tests::rejects_reordered_prerequisites_and_a_shared_prerequisite_child`,
  `src/evidence_validation.rs::tests::rejects_linked_implementation_type_scheme_and_provenance_corruption`,
  `src/evidence_validation.rs::tests::rejects_missing_and_reordered_same_typed_implementation_method_slots`,
  `src/evidence_validation.rs::tests::rejects_imported_implementation_route_without_its_exact_direct_edge`,
  and
  `src/evidence_validation.rs::tests::rejects_inference_forall_and_out_of_scope_type_escape_in_selected_goals`.

### Core order, recursive binders, validation staging, and closed inventories

- [`tests/interfaces.rs`](../../../tests/interfaces.rs):
  `tests/interfaces.rs::generic_prerequisite_evidence_has_a_bounded_unspecialized_evaluation_trace`.
- [`tests/recursion.rs`](../../../tests/recursion.rs):
  `tests/recursion.rs::implementation_methods_share_mutual_recursive_scope`.
- [`tests/architecture.rs`](../../../tests/architecture.rs):
  `tests/architecture.rs::core_and_evaluator_keep_interface_evidence_outside_their_closed_inventories`
  and
  `tests/architecture.rs::synthesis_block_exit_releases_original_state_after_macro_shadow_drop`.
- [`src/evidence_validation.rs`](../../../src/evidence_validation.rs):
  `src/evidence_validation.rs::tests::validated_interface_capability_has_exact_resolved_program_payload`
  compiler-checks the capability's exhaustive payload shape.
- [`src/driver.rs`](../../../src/driver.rs):
  `src/driver.rs::tests::injected_evidence_failure_stops_before_core_synthesis_consumers`
  and
  `src/driver.rs::tests::independent_core_validation_starts_with_only_the_core_registry_owner`.

### Exact end-to-end observations

- [`tests/interface_corpus.rs`](../../../tests/interface_corpus.rs):
  `tests/interface_corpus.rs::local_equal_int_observes_true`,
  `tests/interface_corpus.rs::cross_module_constrained_equal_observes_true`,
  `tests/interface_corpus.rs::generic_option_evidence_observes_true`,
  `tests/interface_corpus.rs::hidden_carrier_composes_to_forty_two`,
  `tests/interface_corpus.rs::opaque_carrier_uses_public_operations`,
  `tests/interface_corpus.rs::recursive_impl_method_computes_forty_two`, and
  `tests/interface_corpus.rs::mutual_impl_methods_compute_forty_two`.
- [`tests/interfaces.rs`](../../../tests/interfaces.rs):
  `tests/interfaces.rs::top_level_function_with_nested_function_domain_completes_the_pipeline`
  observes `42 : Int` after implementation checking, selection, lowering,
  validation, and evaluation.

### Deterministic diagnostics, causal labels, and no private leak

- [`tests/interface_diagnostics.rs`](../../../tests/interface_diagnostics.rs):
  `tests/interface_diagnostics.rs::imported_method_failure_relates_public_cause_without_leaking_private_impl`,
  `tests/interface_diagnostics.rs::constrained_import_failure_does_not_leak_a_transitive_impl_route`,
  `tests/interface_diagnostics.rs::qualified_method_failure_relates_the_import_alias_used_by_the_occurrence`,
  `tests/interface_diagnostics.rs::targeted_global_failure_relates_the_import_binding_used_by_the_occurrence`,
  `tests/interface_diagnostics.rs::nested_unsatisfied_failure_retains_the_selected_implementation_chain`,
  and
  `tests/interface_diagnostics.rs::concrete_prerequisite_cycle_retains_each_selected_implementation_chain`.
- [`tests/module_cli.rs`](../../../tests/module_cli.rs):
  `tests/module_cli.rs::cli_renders_the_structured_interface_diagnostic_without_reclassifying_it`.

### Graph-wide resources, exact boundaries, cycles, and stack safety

- [`tests/interface_resources.rs`](../../../tests/interface_resources.rs):
  `tests/interface_resources.rs::one_constraint_budget_persists_from_dependency_admission_through_validation`
  and
  `tests/interface_resources.rs::cycle_precedes_constraint_resource_exhaustion_after_import_admission`.
- [`src/elaborate.rs`](../../../src/elaborate.rs):
  `src/elaborate.rs::tests::one_type_budget_spans_all_checked_modules`,
  `src/elaborate.rs::tests::one_constraint_budget_spans_all_checked_modules`,
  `src/elaborate.rs::tests::impl_method_substitution_uses_the_exact_constraint_budget`,
  `src/elaborate.rs::tests::imported_overlap_uses_retained_route_order_and_exact_budget`,
  and
  `src/elaborate.rs::tests::invalid_outer_method_shape_has_an_exact_stack_safe_constraint_boundary`.
- [`src/evidence.rs`](../../../src/evidence.rs):
  `src/evidence.rs::tests::every_same_interface_candidate_inspection_is_constraint_bounded`,
  `src/evidence.rs::tests::ground_prerequisite_reentry_is_a_cycle_before_resource_exhaustion`,
  and
  `src/evidence.rs::tests::deep_ground_prerequisite_chain_selects_and_drops_on_a_small_stack`.
- [`src/evidence_audit.rs`](../../../src/evidence_audit.rs):
  `src/evidence_audit.rs::tests::traversal_budget_has_an_exact_boundary_before_checked_wrapping`.
- [`src/evidence_validation.rs`](../../../src/evidence_validation.rs):
  `src/evidence_validation.rs::tests::one_constraint_budget_continues_from_linking_through_validation`.
- [`src/interface.rs`](../../../src/interface.rs):
  `src/interface.rs::tests::evidence_builder_charges_nodes_and_ordered_slots_before_retention`
  and
  `src/interface.rs::tests::flat_evidence_plan_and_deep_substitution_drop_on_a_small_stack`.
- [`src/core/dialect.rs`](../../../src/core/dialect.rs):
  `src/core/dialect.rs::tests::type_abstraction_binders_consume_the_exact_builder_budget`.
- [`src/core/validate.rs`](../../../src/core/validate.rs):
  `src/core/validate.rs::tests::linear_type_scope_chain_uses_the_exact_proportional_budget`.
- [`tests/interfaces.rs`](../../../tests/interfaces.rs):
  `tests/interfaces.rs::deep_generic_prerequisite_chain_completes_the_pipeline_on_a_small_stack`.

### Normative examples and bounded baseline trace

- [`tests/spec_examples.rs`](../../../tests/spec_examples.rs):
  `tests/spec_examples.rs::overview_local_interface_evidence_example_is_executable`,
  `tests/spec_examples.rs::overview_cross_module_constrained_example_is_executable`,
  `tests/spec_examples.rs::static_semantics_generic_prerequisite_evidence_example_is_executable`,
  `tests/spec_examples.rs::resolution_hidden_carrier_interface_example_uses_public_operations`,
  `tests/spec_examples.rs::resolution_opaque_carrier_interface_example_uses_public_operations`,
  `tests/spec_examples.rs::syntax_constrained_global_presentations_are_executable`,
  and `tests/spec_examples.rs::normative_document_manifest_is_complete`.
- [`tests/interfaces.rs`](../../../tests/interfaces.rs):
  `tests/interfaces.rs::generic_prerequisite_evidence_has_a_bounded_unspecialized_evaluation_trace`.

## Diagnostics, provenance, and privacy

Constraint diagnostics retain the selected source occurrence as primary and a
typed causal chain through its interface declaration, exact admitted import,
selected implementation, and implementation method. Qualified and targeted
occurrences retain the import alias or selector item actually used; another
route to the same stable declaration is not substituted for it. Nested
unsatisfied prerequisites and cycles retain the declaration-ordered selected
implementation chain.

Diagnostic provenance is intentionally narrower than semantic summary closure.
A private dependency implementation is unavailable and its source span does
not enter an importer diagnostic. A public implementation available only to an
intermediate direct dependent is not exposed as a transitive route. A hidden
foreign-interface shape can authenticate a public fact without re-exporting
the public interface, while a hidden private nominal identity does not make its
spelling or constructors available. Neither closure makes implementation
bodies or import paths renderable to the caller. Existing structured reason
ownership and CLI rendering remain in place.

## Resources and stack ownership

One driver-owned constraint-work budget spans imported summary admission,
checking across the graph, linking, and linked interface-evidence validation.
The implementation charges retained facts and planned work before allocation
or traversal. Imported overlap follows authenticated route order. Candidate
inspection is bounded even for a wide same-interface environment, and evidence
construction charges nodes and ordered slots before retaining them. The linked
validator continues the same budget rather than resetting it at the stage
boundary.

This interface-and-constraint budget is distinct from existing inference,
Core-construction, and Core-validation budgets. Resolution and checking retain
their existing type-work budgets for inference and type storage. No Core node
is constructed until linked interface-evidence validation succeeds. Core
synthesis then uses the existing bounded Core builder, and the independently
bounded Core validator checks the completed program afterward. An interface-
evidence failure therefore stops before both Core-construction and
Core-validation work; neither Core budget is spent to authenticate interface
metadata.

Cycle detection owns semantic failure precedence over later resource
exhaustion. Properly decreasing generic prerequisite chains use explicit work
stacks. Evidence plans, deep substitutions, checked-body audits, selection
chains, validator worklists, rejected payloads, and replacement paths have
small-stack destruction witnesses. These cases make the bound graph-wide and
independent of module partitioning or recursive Rust call depth.

Removing recursive nested-arrow search changes the exact checker boundaries.
One interface exhausts the shared constraint budget at 36 units and succeeds at
37. An implementation-method substitution exhausts it at 76 and succeeds at
77. The 10,000-level invalid outer-method fixture exhausts its local check at 7
and reaches `interface.method-not-function` at 8 on a 64 KiB stack. Dropping
that fixture also exercises `ResolvedModule::drop` and
`discard_resolved_interface_iteratively`, so the rejected resolved type is not
destroyed through recursive Rust calls.

## Facts retained and released

| Boundary | Facts retained | Facts released |
| --- | --- | --- |
| Source projection to resolution | ordered declarations, requirements, prerequisites, equations, source spans | parser recovery state and unused concrete-tree structure |
| Resolution to checking | stable semantic identities, resolved heads and schemes, exact import provenance, occurrence-local empty evidence slots, imported body-free facts | aliases as semantic identity, unavailable private names, mutable namespace search state |
| Checking to dependency summaries | public interface and method facts, public implementation heads, checked schemes, ordered prerequisites and mappings, hidden nominal/interface closure, provenance | bodies, private scope, private implementations, and implementations imported by the publisher |
| Checking to linking | complete checked groups and bodies, defining registries, filled structural occurrences, per-module availability and dependency edges | selection search work and inference state after obligation closure |
| Linking to interface-evidence validation | combined checked groups and registries, structural plans, occurrence module and import route, stable identities, scope/type/provenance facts | module-local assembly state |
| Validated evidence to Core synthesis | authenticated checked definitions and evidence capability | the validator-local linked-interface registry and validation indexes after successful authentication |
| Core synthesis to Core validation | synthesized ordinary Core with its resolved registry, source provenance, the result type, and its computed source-facing display | the validated interface program, checked bodies, structural evidence, routes, the display-registry clone, and remaining interface identities when the explicit typed synthesis scope exits; an eager wrapper drop remains inside that scope |
| Core validation to evaluation | one validated ordinary pure Core program | Core validator indexes and all remaining static evidence facts |

Source syntax erases separately from semantic identity. Import spellings and
interface declarations cease to be source operations after resolution, while
their stable identities remain through checking and linked evidence validation.
Linked evidence validation builds its registry locally, uses it to authenticate
occurrences, and does not store it in the validated capability. Core synthesis
borrows that capability inside an explicitly typed driver block. The block also
owns the display-registry clone, type-display computation, synthesis finish,
and the eager wrapper drop. The drop records the last intentional capability
use; block exit is the ownership boundary before independent Core validation.
Only `Type`, `String`, and `UnvalidatedProgram` cross it. Compiler-exhaustive
destructuring checks the capability's exact `ResolvedModuleProgram` payload,
and a driver weak-reference witness proves that only the unchecked Core program
owns the resolved registry when Core validation begins. The authenticated
relationships have already become ordinary Core structure, so this boundary
releases checked bodies, evidence, routes, the display clone, and remaining
checked interface metadata without changing Core or evaluation. The linked
validator's registry and indexes already ended locally after successful
authentication.

## Locality and maintenance

Interface-specific semantic machinery is concentrated in these production
boundaries:

- [`src/interface.rs`](../../../src/interface.rs) owns identities, constrained
  schemes, flat plans, head matching, and their local resource accounting;
- [`src/resolve.rs`](../../../src/resolve.rs) and
  [`src/resolved.rs`](../../../src/resolved.rs) own namespace identity, summary
  closure, import availability, occurrence slots, and provenance;
- [`src/elaborate.rs`](../../../src/elaborate.rs) owns declaration and
  implementation checking, linking, and Core synthesis;
- [`src/evidence.rs`](../../../src/evidence.rs) and
  [`src/evidence_audit.rs`](../../../src/evidence_audit.rs) own structural
  selection and checked-body completeness;
- [`src/evidence_validation.rs`](../../../src/evidence_validation.rs) owns the
  independent pre-Core authenticity boundary; and
- [`src/driver.rs`](../../../src/driver.rs) orders linking, evidence validation,
  Core synthesis, Core validation, and evaluation under the graph-wide budget.

The stable maintenance search

```text
rg -l '\b(InterfaceId|MethodId|ImplId|ImplMethodId|RequirementId|EvidenceSelection|ConstrainedScheme|validate_interface_evidence)\b' src
```

returns exactly those eight production files. Surface grammar and projection
remain at the existing lexer/parser boundaries. Core and evaluator source are
protected by the closed-inventory architecture guard rather than by a parallel
interface dispatch subsystem.

## Findings retained and released

Retained findings are:

- stable semantic identities, rather than paths or spans, are the transferable
  currency across summaries, alternate routes, linking, and validation;
- a body-free summary needs hidden checked identity closure distinct from
  public source nameability;
- direct dependency edges own implementation availability, while alternate
  direct routes deduplicate one implementation identity and intermediaries do
  not re-export it;
- occurrence-local one-shot evidence lets selection happen at its checking
  owner and survive without a span-keyed side table or lowering-time search;
- an independent pre-Core validator is required because a structural plan alone
  cannot authenticate linked identity, route, scheme, scope, type, and
  provenance claims;
- flattened lexical functions preserve method order and prerequisites without
  requiring a dictionary value or evaluator dispatch rule; and
- a graph-wide resource budget must cross summary admission, checking, linking,
  and validation to remain independent of module partitioning.

Released alternatives are source dictionaries, span-keyed evidence maps,
lowering-time reselection, implementation re-export, summaries containing
bodies or private scopes, route-specific implementation identities, runtime
registries, and a new interface Core or evaluator family.

## Exclusions and downstream pressure

This increment does not add associated types, projections, normalization,
multi-parameter or higher-kinded interfaces, default methods, specialization,
priorities, negative implementations, first-class source dictionaries, named
implementation values, interface objects, module signatures, inferred exported
requirements, constrained `main`, cross-module recursion, dynamic loading,
registration, discovery, a new Core node, a new evaluator rule, or dead-code
elimination.

Its retained unspecialized trace and closed inventory provide a baseline for a
later, separately authorized core-versus-library audit. That audit may compare
an existing Core behavior with a library interface after this increment is
complete and specified. This work does not begin the audit, choose a migration,
or authorize specialization.

## Review and verification checkpoint

The final reviewed product checkpoint is unsigned commit
`ee998a05e9783972dc9952024fce2720b5d41449`. Independent branch-wide reviews of
language semantics and specification, Rust implementation and resource bounds,
documentation authority and provenance, and current-`main` integration are
clear after the findings below passed their fix and re-review loops. This report
and transition cleanup record that checkpoint; they do not move the product
boundary.

The original increment's reviewed product checkpoint was unsigned commit
`37ef9f8`. It included the unsigned namespace fix `5398808` and
evidence-validator fix `37ef9f8`. Unsigned commit `07b9129` recorded the
finalized evidence report for that original checkpoint without moving its
product boundary. The findings remain below as historical provenance.

The original increment's review found that targeted interface and method maps
were absent from four local conflict gates. This allowed a targeted interface
to conflict with a same-spelled local interface or nominal, and a targeted
method to conflict with a same-spelled local method or renamed constructor.
Commit `5398808` adds the four missing checks. Four focused TDD integration
tests witnessed RED before the fix and GREEN after it.

That review also found that linked evidence validation authenticated a
selected node's individual facts without authenticating selection order. It
accepted a concrete implementation over an identity-equal lexical abstract
requirement, a freshly instantiated current implementation at the root or below
another node, and a later duplicate abstract requirement out of source order.
The validator also rejected a valid exact-current selection with repeated
identity-equal prerequisites. Commit `37ef9f8` reconstructs the required order
with ordered
`RequirementId` lookup, exact rigid current-identity substitution, exclusion of
the current implementation when it is not exact, and mandated prerequisite
`RequirementId`s below an exact-current node. Six focused selection-order
behavior tests captured the RED findings and valid guards, then passed GREEN
after the fix. Exact resource tests place the abstract-priority scan at 6
constraint-work units and exact-current authentication with its mandated
abstract prerequisite at 67 units; one unit less fails and the exact limit
passes at that original checkpoint.

Later branch-wide review found that linking authenticated individual checked
modules but not the selected entry's exact module closure. It accepted an
omitted direct dependency, a dependency after its importer, an unrelated module,
and a surplus module that depended on the selected entry. Commit `8a37934`
requires dependencies before their importers and requires the linked modules to
equal the selected entry's complete dependency closure. Four integration tests
retain those malformed boundaries.

Review also found that a filled occurrence slot retained selected evidence
without independently retaining the checker-zonked obligation argument. A
forged selection could therefore authenticate its own goal while disagreeing
with the checked occurrence. Commit `d55366a` atomically retains the checked
goal and selection in the one-shot evidence slot, and linked validation checks
their equality before Core synthesis. Focused negative, exact-budget, clone,
and small-stack tests retain that authentication boundary.

The language review then found that arrow-anywhere interface admission accepted
a method type that no positive-pattern implementation equation could check.
Commit `364c736` requires `Function` as the outermost method-type constructor,
preserves `interface.method-parameter` precedence, rejects a nested-only arrow,
retains top-level functions with nested function domains and codomains, checks
the implementation failure boundary, and completes a `42 : Int` end-to-end
case.

Commit `18c04fd` remeasures the resource cost after removing recursive
nested-arrow search. One interface exhausts the constraint budget at 36 units
and succeeds at 37; implementation-method substitution exhausts it at 76 and
succeeds at 77; and the 10,000-level invalid outer-method fixture exhausts its
local check at 7 and reaches `interface.method-not-function` at 8 on a 64 KiB
stack. `ResolvedModule` destroys the rejected interface payload iteratively, so
the same fixture also retains stack-safe teardown evidence.

Unsigned merge `78c6da9` incorporates current `main` and reconciles DN-0024,
the design index, and the trajectory with implemented Modular Ash. Commits
`089c54e`, `5210beb`, and `ee998a0` then align the normative specification,
retained evidence, task progress, and historical checkpoint provenance with the
outer-`Function` correction. Repeated language, Rust and resource,
documentation, and integration review found no remaining actionable defect at
`ee998a0`.

The complete verification boundary passes at `ee998a0`:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo clippy --locked --all-targets -- -D warnings
cargo xtask verify
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

The locked all-target test inventory is exactly 927 tests: 298 library tests,
10 binary tests, and 619 integration tests. The canonical `cargo xtask verify`
workspace verifier additionally runs xtask's own one-test unit suite. Manual
relative-link, authority-boundary, and formal-notation audits also pass.

Complete-branch inspection from current `main` at `8f4de9a` to `ee998a0` covers
133 files, 45,894 insertions, and 5,327 deletions. Current `main` is an ancestor;
the branch is 51 commits ahead and 0 behind. Interface-increment inspection
from `ca79328` through `ee998a0` covers 72 files, 31,180 insertions, 3,492
deletions, and 31 commits. The search

```text
rg -n '\b(Interface|Impl|Requirement|EvidenceSelection)\b' src/core src/eval
```

returns no matches. The stable maintenance search still returns exactly the
eight production files listed above, and the Core and runtime enum inventories
remain unchanged from `ca79328`. The worktree was clean at the reviewed product
checkpoint.

Transition cleanup is complete in this report-and-cleanup commit: the completed
proposal, task, execution plan, their index entries, and all live links to them
have been removed. Git retains their history. This cleanup does not move the
`ee998a0` product boundary. The product remains unmerged into `main`, although
current `main` at `8f4de9a` is incorporated and remains an ancestor. The
retained unspecialized trace supplied the baseline for the separately
authorized core-versus-library comparison. That audit is complete and retained
in the [core-and-library evidence](core-library-evidence.md).
