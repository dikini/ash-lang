# Explicit Kinds and Higher-Kinded Parameter Evidence

This report records implementation evidence for the second bounded `lib-ash`
increment: explicit kinds and higher-kinded declaration parameters. It is
informative, not normative. The [Ash specification](../../../spec/README.md)
alone defines the current language. The accepted proposal, task, design record,
and execution plans remain transition artifacts until the reviewed product
checkpoint retains their results and removes them.

This report does not close the complete `lib-ash` milestone. Method-local type
parameters, multi-parameter interfaces, determination, associated outputs,
defaults, the combined library corpus, and the final library simplification
audit remain separate work. This increment receives no `lib-ash` tag.

## Scope and checkpoints

The branch starts from integrated explicit-import checkpoint `a1647ff`. Its
principal unsigned product checkpoints are:

- `a6cae23`, which retains explicit kind syntax and declaration binder lists;
- `f71424e`, which replaces saturated semantic nominal applications with one
  canonical unary application tree;
- `040f4d5`, which gives resolved declarations fixed kinds and one total kind
  gate;
- `3c3ffdb`, which makes Core schemes, abstraction, application, transforms,
  and independent validation kind-aware;
- `b94ac52`, which preserves fixed kinds through inference, unification, local
  generalization, and checked value-scheme admission;
- `e411ed7`, which makes implementation matching and evidence selection
  first-order and kind-preserving;
- `7a1bd84`, which authenticates kinded body-free and linked facts;
- `0794457` through `5cc441d`, which retain ordered resolved-global binder
  authority, close generated-binder and transform evidence, and close the
  linked Core resource and tampering matrices;
- `41b98f7`, which closes diagnostic, public resource, and deep-disposal
  evidence;
- `0af2350`, which proves predecessor migration and the linked product corpus;
  and
- `8c11cd3`, which restores the documented module-wide source order of resolved
  type-binder identities across interleaved declaration families.

These commits are implementation evidence, not independent language authority.
The Task 12 specification checkpoint and Task 13 final review, retention, and
lifecycle cleanup remain to be recorded when their gates finish.

## Implemented boundary

The kind language has `Type` and right-associative function kinds. Declaration
binders may carry an explicit kind:

```ash
type Option<A> =
    None
    | Some(A)

keep<F : Type -> Type, A> : F<A> -> F<A>
keep value = value
```

Nominal, interface, global, operational, and implementation declarations retain
their written binder order. A present global or implementation binder list is
complete: every binder used by that declaration header must appear exactly
once, and every listed binder must be used there. When the list is absent, the
resolver introduces binders from free type names in first-occurrence order.

Every omitted declaration kind annotation, and every binder introduced by an
omitted global or implementation binder list, is fixed to `Type`. Ash does not
infer a kind for those binders. This is the current phase-dependent language
constraint, not a commitment against a later bounded declaration-local
inference rule.

The increment adds neither kind polymorphism nor type lambdas. It does not infer
function kinds from application, perform higher-order unification, or introduce
source `forall` or explicit term type application.

## Canonical identities and applications

Each resolved source type binder receives a module-qualified identity whose
local ordinal follows source order across nominal, interface, global, and
implementation declaration families. Written binder order and implicit
first-occurrence order remain owner-local authority. The regression at
`8c11cd3` proves both properties when parameterized families interleave; strict
Core registry validation continues to reject forged identity-to-source order.

Surface type application may retain several comma-separated arguments, but
resolution folds them left into the one canonical unary form:

```text
F<A, B>  =  Application(Application(F, A), B)
```

This structural application is not Core scheme instantiation. One Core
`TypeApplicationNode` supplies all arguments to one complete outer rank-1
scheme simultaneously. Tests reject partial outer-scheme instantiation while
admitting partial nominal or variable application when the surrounding kind
expects the residual function kind.

## Kind environments and checking

The shared total kind engine uses four fixed environments:

- `DELTA` maps declaration or generated scheme binders to declared kinds;
- `OMEGA` maps transient inference identities to their fixed kinds;
- `XI` maps canonical nominal identities to derived or frozen kinds; and
- `IOTA` maps interface identities to their canonical parameter record,
  including its `TypeVariableId` and declared Kind.

Primitive types synthesize `Type`. Variables and inference identities use
`DELTA` and `OMEGA`. Nominals use `XI`. Unary application requires a function
kind whose domain equals the argument kind and returns its residual codomain.
Tuple and function components must have kind `Type`, and the complete tuple or
function type also has kind `Type`. Ordinary value annotations require `Type`.
An interface argument is checked against the selected interface parameter's
declared kind rather than the ordinary value-type rule.

One resolved kind stage derives every local nominal kind before it checks any
type-bearing declaration fact. The stage authenticates canonical binder records,
constructor payloads, interface methods, globals, requirements, implementations,
and declaration-order completeness before `ResolvedModule` construction.
Checked schemes and body-free facts retain ordered identity-kind pairs.

## Inference, matching, and evidence

Every fresh inference identity receives one fixed `OMEGA` entry before the
identity appears in a type. Ordinary fresh identities have kind `Type`; scheme
instantiation and constructor patterns copy the defining binder kind. Eligible
local generalization copies fixed kinds into generated outer-scheme binders.
Recursive and otherwise ineligible locals remain monomorphic.

Unification remains first-order. Before it publishes a solution it checks the
candidate against the inference identity's fixed kind. It traverses both
children of canonical applications and admits partial constructors without
synthesizing a type lambda. Zonk and generalization preserve those fixed kinds
and reject missing, duplicate, conflicting, or escaping inference facts.

Implementation matching treats goals as rigid and binds only candidate
parameters. Each retained substitution must have the defining binder's kind.
Overlap independently freshens both candidates. Selection admits only complete,
inference-free interface goals and preserves abstract, exact-current, then
concrete candidate priority. Prerequisites, selected roots, substitutions,
checked methods, and occurrence evidence are authenticated again at their
owning boundaries.

## Summaries and linked facts

A checked dependency publishes body-free kind facts only after its complete
body succeeds. Transparent nominals retain their ordered parameters and
constructor family. Hidden and opaque nominals retain frozen body-free kind
facts without exposing constructors or materializing private declaration rows.
Imported interface, global, and implementation facts retain the exact defining
identities and kinds used by checking and evidence selection.

Physical constructor schemes have one transfer lifecycle:

```text
checked export summary -> imported fact -> disposal before linked Core
```

The linker does not retain a redundant constructor-scheme carrier. Linked
nominal and constructor registry facts are sufficient for independent Core
kind derivation after authenticated summaries have been consumed.

Linked evidence validation checks every canonical type-variable record, nominal
family, interface fact, global scheme, implementation fact, selected evidence
root, substitution, method, route, and occurrence before it exposes the
capability used for Core synthesis. A failed check publishes no validated
program.

## Linked Core authority

[AD-0009](../../decisions/AD-0009-ordered-resolved-global-binder-authority.md)
accepts one private ordered owner-to-parameter fact in the shared immutable
registry for each non-empty resolved global scheme. The fact contains only the
stable term owner and ordered resolved parameter identities. Canonical
variable records remain the only authority for kind, spelling, and source
origin.

This is an implementation boundary, not language syntax or a normative storage
model. The specification requires the observable validation relationship: a
resolved outer abstraction must be the immediate initializer of its owning
`RecursiveBind` member, its identities and order must equal the authenticated
global scheme exactly once, and every authenticated owner must be consumed.
The specification does not expose the private row type, its position index, or
its physical storage.

A sequential Core `Bind` cannot claim resolved-global authority. Nominal
parameters retain their separate ordered nominal ownership. Interface binders
erase before Core. Implementation-method parameters and locally generalized
binders use generated Core identities.

Generated Core identities are local to their `TypeAbstractionNode`, matching
outer `Forall`, lexical body, and applications. A complete capture-free fresh
substitution is valid alpha-renaming. Independent validation does not
authenticate the elaborator's original generated identity, source span, or
allocation ordinal as external authority.

Both identity traversal and literal folding rebuild expression nodes while
sharing the immutable registry. Each result passes fresh module-aware Core
validation. Kinds, schemes, abstractions, applications, and resolved-owner
facts erase before evaluation. No evaluator value, frame, lookup, transition,
or failure mode changes.

## Diagnostic matrix

| Invalid relationship | Owning phase and reason |
| --- | --- |
| malformed kind syntax or binder-list syntax | `parse.*` |
| duplicate, unused, or omitted explicit declaration binder | `resolve.duplicate-type-parameter`, `resolve.unused-type-parameter`, or `resolve.unknown-type` |
| interface used as an ordinary value type | `resolve.type-kind` |
| non-interface used where an interface is required | `resolve.interface-kind` |
| unsaturated constructor at a value-type boundary | `kind.expected-type` |
| applying a `Type`-kinded binder as a constructor | `kind.not-applicable` |
| application domain or interface argument kind mismatch | `kind.argument` |
| inference unification mismatch or infinite type | existing `type.*` owner after fixed-kind authentication |
| absent, ambiguous, or cyclic interface evidence | existing `constraint.*` owner |
| malformed checked, summary, or linked kind mirror | `evidence.validation.*` before Core |
| malformed Core kind, scope, owner, order, provenance, or registry relation | `core.validation.*` before evaluation |

Library and CLI diagnostic tests assert reason codes, primary spans, expected
and found kinds, declaration labels, route labels, and stage ownership. The
migration corpus records deliberate predecessor stage changes from nominal
arity or resolution failures to total kind failures; it does not normalize all
failures to one generic error.

## Named semantic evidence

The positive and negative boundary is retained by named tests rather than by
the prose alone:

- `projects_contextual_kinds_and_explicit_binders`,
  `malformed_kind_and_binder_headers_recover_without_projection`, and
  `legacy_headers_remain_distinct_from_present_explicit_lists` in
  [`tests/kinds_syntax.rs`](../../../tests/kinds_syntax.rs) cover syntax,
  recovery, spans, contextual `Type`, and list omission.
- `explicit_kind_binders_are_complete_and_ordered`,
  `declaration_type_binder_identities_follow_source_order_across_interface_and_nominal_families`,
  `declaration_type_binder_identities_follow_source_order_across_impl_and_global_families`,
  `explicit_global_binders_reject_duplicates_unused_names_and_omissions`, and
  `explicit_implementation_binders_reject_duplicates_unused_names_and_omissions` in
  [`tests/resolution.rs`](../../../tests/resolution.rs) cover binder sets,
  order, scope, and structured resolution failures.
- `total_resolved_kinding_accepts_every_type_form_and_value_site`,
  `omitted_lists_do_not_infer_arrow_kinds_in_this_phase`,
  `bare_nominal_in_a_value_type_reports_structured_expected_type`,
  `applying_a_type_kinded_binder_reports_not_applicable`, and
  `application_domain_mismatch_reports_argument_kind_and_declaration` in
  [`tests/kinds.rs`](../../../tests/kinds.rs) cover total synthesis,
  phase-dependent fixed kinds, diagnostics, and precedence.
- `higher_kinded_instantiation_preserves_fixed_kinds` and
  `eligible_local_relay_generalizes_higher_kinded_parameters` in
  [`tests/polymorphism.rs`](../../../tests/polymorphism.rs), together with
  `inference_kind_registry_rejects_missing_duplicate_and_conflicting_entries`
  and `deep_kind_authenticated_unification_has_an_exact_stack_safe_budget` in
  `src/elaborate.rs`, cover inference, generalization, zonking, unification,
  and escape prevention.
- `allows_distinct_higher_kinded_partial_heads`,
  `rejects_overlapping_higher_kinded_partial_heads`,
  `higher_kinded_concrete_candidate_retains_ordered_substitution_and_evidence`,
  and `ordinary_candidate_search_does_not_refine_a_rigid_higher_kinded_goal`
  in [`tests/implementations.rs`](../../../tests/implementations.rs) and
  [`tests/interface_selection.rs`](../../../tests/interface_selection.rs)
  cover first-order matching, overlap, prerequisites, rigid goals, and
  selection.
- `detached_summaries_preserve_defining_kinds_across_every_import_route` in
  [`tests/kind_modules.rs`](../../../tests/kind_modules.rs),
  `deep_constructor_scheme_crosses_check_and_link_then_is_disposed_before_core`
  in `src/evidence_validation.rs`, and
  `authenticates_one_reusable_higher_kinded_linked_diamond` in the same file
  cover body-free facts, hidden closure, route reuse, and constructor-scheme
  disposal.
- `linked_higher_kinded_core_revalidates_after_both_transforms` in
  [`tests/core_validation.rs`](../../../tests/core_validation.rs),
  `higher_kinded_interface_erasure_adds_no_runtime_state_or_transition` in
  [`tests/interfaces.rs`](../../../tests/interfaces.rs), and
  `wide_source_argument_vector_crosses_body_free_link_and_core_on_a_small_stack`
  in [`tests/kind_resources.rs`](../../../tests/kind_resources.rs) cover the
  final linked program, both transforms, independent validation, erasure,
  evaluation, and wide folded application.
- `public_kind_diagnostics_retain_complete_causal_rows` in
  [`tests/diagnostics.rs`](../../../tests/diagnostics.rs),
  `public_kind_failure_precedence_follows_causal_and_owner_order` in the same
  file,
  `cli_renders_each_structured_kind_reason_without_reclassifying_it` in
  [`tests/module_cli.rs`](../../../tests/module_cli.rs),
  `explicit_kind_migration_matrix_records_every_predecessor_assertion_shift`
  and `every_valid_corpus_presentation_has_its_exact_library_and_cli_observation`
  in [`tests/corpus.rs`](../../../tests/corpus.rs), and the 57 tests in
  [`tests/spec_examples.rs`](../../../tests/spec_examples.rs) cover diagnostics,
  CLI policy separation, migration, normative examples, and exact
  observations.

## Migration

Every predecessor-valid omitted kind annotation and absent global or
implementation binder list remains valid without source edits. Omitted binders
retain `Type` and their prior owner-local order. Explicit `Type` annotations and
explicit lists are compatible spellings of that boundary.

The compatibility corpus proves exact library and CLI observations for:

- omitted nominal, interface, global, operational, and implementation kinds;
- implicit global and implementation binder order;
- explicit `Type` annotations and explicit list order;
- contextual nominal `Type` beside kind `Type`;
- ordinary rank-1 instantiation and higher-kinded partial application; and
- linked modules using explicit implementation imports from the predecessor
  increment.

Intentional migrations replace saturated-shape assumptions with canonical
application inspection and replace predecessor kind-blind failures with the
structured kind reasons above. No compatibility grammar or second compiler
path remains.

## Type-bearing inventory

[`tests/architecture.rs`](../../../tests/architecture.rs) keeps the production
type-and-kind inventory at a bidirectional fixed point. At checkpoint `8c11cd3`
it records 755 kind sites:

| Site class | Count | Meaning |
| --- | ---: | --- |
| physical fields | 697 | stored production carriers whose ownership, rule, failure, budget, and disposal are recorded |
| contextual uses | 33 | one physical carrier interpreted under more than one kind obligation |
| transient work owners | 25 | local stacks, continuations, and completed-work buffers |

Each `KIND_SITES` entry names its source carrier, environment, owning rule,
required result, failure class, budget, disposal owner, and contextual roles.
The retained test manifest is the complete per-site map; this report records
its reviewed totals rather than duplicating 755 independently stale rows.

Sixteen shared Kind-engine sites are phase-neutral: their caller supplies the
phase-owned failure and budget. The inventory also rejects broad raw mutation
of recursive type owners, stale manifest entries, unrecorded production fields,
and Core or evaluator interface-evidence state. Task 13 must refresh these
counts if review changes a production carrier.

## Exact resources and disposal

The increment changes one production capacity: independent Core validation
uses one cumulative `3 * TYPE_WORK_LIMIT = 983,040` ledger instead of the
predecessor's `TYPE_WORK_LIMIT` ledger. This preserves the unchanged deep and
wide predecessor witnesses after kind validation enters the same cumulative
pass. Core construction, transform rebuilding, and every other production
limit retain their predecessor capacities. No later task resets, splits,
raises, or narrows those limits.

The retained exact formulas and their executable owners are:

| Boundary | Additive work or measured result | Named proof |
| --- | --- | --- |
| Kind fold, clone, equality, hash, and render | `K` units for a retained or visited `K`-node Kind; folding also retains one `Arrow` per domain | `kind_algebra_is_iterative_and_exactly_budgeted` in `src/types.rs` |
| Type clone, equality, hash, and render | `C` units for a visited or retained `C`-cell Type | `deep_application_operations_remain_bounded_on_a_small_stack` in `src/types.rs` |
| Type and Kind disposal | one visit per structural cell; pending ownership is the left-spine depth or sequence width | `type_and_kind_disposal_have_exact_visits_and_bounded_pending_ownership` in `src/types.rs` |
| Type substitution | the complete rebuilt result cell count; a depth-`D` unary application costs `2D + 1` and a width-`W` tuple costs `W + 1` | `deep_and_wide_substitution_resource_boundaries_are_exact_and_reusable` in `src/types.rs` |
| one declared or copied binder | `1 + K` type units for the binder record and its `K` Kind nodes | `fixed_kind_binder_allocation_is_exact_and_atomic` in `src/resolve.rs` and `copied_fixed_kind_binder_storage_is_exact_and_atomic` in `src/resolved.rs` |
| materialized nominal Kind retention | `2 + sum_parameter(1 + K_i)` type units per nominal | `linked_nominal_kinds_are_retained_once_for_all_value_schemes` in `src/evidence_validation.rs` |
| checker-view abstract nominal Kind retention | the same parameter-derived Kind has an exact atomic budget and remains non-structural | `checker_view_retains_abstract_kind_without_structural_visibility` and `checker_view_abstract_kind_failure_and_drop_are_stack_safe` in `src/resolved.rs` |
| imported checker-view declaration binders | `1 + K` type units for one interface binder; `sum_i(1 + K_i)` for implementation-head binders | `checker_view_interface_binder_has_an_exact_atomic_budget_and_preserves_source` and `checker_view_implementation_head_binders_have_an_exact_atomic_budget` in `src/resolved.rs` |
| inference solution | 17 scalar units; `9C - 3D + 8` for a `C`-cell candidate of function depth `D` | `unification_charges_operand_copies_and_solution_metadata_exactly` and `deep_kind_authenticated_unification_has_an_exact_stack_safe_budget` in `src/elaborate.rs` |
| generalization of `n` variables in type `T` | `3n + sum_i(3 + 2K_i) + Z(T)` type units, where `Z` is fused zonk work | `higher_kinded_generalization_batch_is_exact_and_atomic` in `src/elaborate.rs` |
| linked `keep` scheme | 18 structural constraint units, 20 Kind-judgment constraint units, and four owner-environment type units | `linked_value_kind_validation_has_exact_dual_limits` in `src/evidence_validation.rs` |
| width-`W` first-order head match | `18W + 8` constraint units and `W` type units; the scalar fixture is 24/5 | `wide_binding_slots_fit_default_work_and_fail_atomically_one_unit_short` and `kind_preserving_head_match_has_exact_independent_resource_boundaries` in `src/interface.rs` |
| deep match and overlap over `K = 2D + 1` Kind nodes | `2K + 18` and `2K + 22` constraint units; the scalar overlap fixture is 42/5 | `deep_higher_kinded_head_match_has_exact_atomic_small_stack_boundaries`, `deep_higher_kinded_overlap_has_exact_atomic_small_stack_boundaries`, and `canonical_higher_kinded_overlap_is_first_order_and_exactly_bounded` in `src/interface.rs` |
| complete concrete selection | 156 constraint and 20 type units | `full_higher_kinded_selection_has_exact_atomic_dual_limits` in `src/evidence.rs` |
| declaration head plus prerequisite authentication | 12 constraint and four type units | `declaration_head_and_prerequisite_kind_authentication_has_exact_dual_limits` in `src/evidence_validation.rs` |
| selected-root and exact-current evidence | 73 units as `59 + 9 + 4 + 1`, and 107 as `87 + 15 + 4 + 1` | `selected_root_and_prerequisite_kind_checks_have_exact_constraint_limit` in `src/evidence_validation.rs` |
| final substitution precharge and argument cloning | `15W + 8` constraint units; `N + sum_i size(Type_i)` type units for `N` arguments | `selected_substitution_authentication_has_exact_kind_limits` in `src/evidence_validation.rs` and `replacement_map_charges_indexes_and_cloned_arguments_exactly_before_publication` in `src/evidence.rs` |
| shared deep Kind judgment | `6D + 3` valid units and `6D - 1` residual-mismatch units | `deep_linked_value_kinding_is_exact_and_stack_safe` in `src/evidence_validation.rs` |
| complete public linked validation | `9D + 63 + O + 2` constraint units for type/Kind depth `D` and generated-origin depth `O` | `deep_public_linked_value_kinding_fits_the_default_budget_on_a_small_stack` in `src/evidence_validation.rs` |
| resolved-global owner-row retention | `2S + R` type units for `S` non-empty owners and `R` identities, plus `S` constraint units for owner uniqueness | `combine_checked_retains_borrowed_global_parameter_rows_in_dependency_order` in `src/resolved.rs` |
| linked row authentication | `S + R` constraint units and no type work; the complete linked-registry fixture costs 23 constraint units | `linked_registry_rows_have_exact_constraint_work_and_no_type_work` in `src/evidence_validation.rs` |
| Core row structure and matching | row structure costs `2S + 2R` type units; resolved matching costs `2R + K_R + S`, where `K_R` is canonical Kind work | `linked_core_row_structure_work_is_exact_atomic_and_retryable`, `complete_linked_core_validation_work_is_additive_exact_and_retryable`, and `linked_arrow_kind_row_matching_work_is_exact_atomic_and_retryable` in `src/core/validate.rs` |
| complete small linked Core validation | 264 cumulative type units: registry 1, row structure 4, envelopes 42, graph 0, binders 16, initializer owners 1, resolved matching 6, generated matching 4, nodes 127, term scopes 0, and type scopes 63 | `complete_linked_core_validation_work_is_additive_exact_and_retryable` in `src/core/validate.rs` |
| independent Core capacity | 983,040 cumulative units; depth-96 uses `275,398 + 145,151 = 420,549`; width-32,767 uses `22W + 7 = 720,881` | `core_validation_type_work_capacity_is_exact_and_atomic` in `src/core/validate.rs`, `deep_generic_prerequisite_chain_completes_the_pipeline_on_a_small_stack` in `tests/interfaces.rs`, and `validated_program_discards_a_wide_application_on_a_small_stack` in `src/core/dialect.rs` |
| unchanged width-256 elaboration and Core witness | `320,221 + 4,883 + 512 = 325,616` of 327,680 type units; 4,096 unrelated `OMEGA` entries do not change reachable solution cost | `wide_nominal_application_remains_width_through_elaboration_and_core` in `tests/polymorphism.rs` and `reachable_solution_cost_is_independent_of_unrelated_omega_width` in `src/elaborate.rs` |
| row-bearing Core construction and transforms | construction costs `3 + 4 + 12 + 9 + 1 = 29`; identity rebuild costs `6 + 8 + 20 + 18 + 2 = 54`; literal folding costs `2 + 8 + 16 + 4 + 18 + 2 = 50`; both transforms add zero copied row units and share the exact immutable registry | `row_bearing_construction_and_identity_have_exact_independent_type_work`, `folded_higher_kinded_transform_has_exact_independent_type_work`, and `unchecked_transforms_share_the_exact_nonempty_global_row_registry` in `src/core/transform.rs` |
| malformed expanded Core resource mapping | width 1,000 expands to at least 1,000,000 retained type cells, exceeds the 983,040 validation ledger while fitting the unchanged construction limit, and reports `ValidationReason::Resource` | `expanded_malformed_type_application_maps_to_validation_resource` in `tests/core_validation.rs` |
| depth-32,000 iterative success and failure teardown | the successful type-application witness costs `11D + 6 = 352,006`; transform, match coverage and redundancy, late-pattern, substituted-payload, downstream-validation, and downstream-evaluator owners all dismantle on 256 KiB stacks | `late_pattern_rebuild_failure_discards_completed_patterns_iteratively` in `src/core/transform.rs`; `successful_type_application_validation_discards_instantiation_work_iteratively`, `successful_match_validation_discards_coverage_matrix_iteratively`, `redundant_match_validation_discards_pending_pattern_row_iteratively`, `late_pattern_validation_error_discards_owned_payload_type_iteratively`, and `payload_shape_error_discards_substituted_type_iteratively` in `src/core/validate.rs`; and `downstream_validation_failure_discards_deep_result_type_iteratively` and `downstream_evaluator_failure_discards_deep_result_type_iteratively` in `src/driver.rs` |

Exact-success, one-short failure, atomic publication, retry, and disposal probes
cover binder allocation, kind synthesis, environments, inference solutions,
generalization, matching, overlap, selection, summary combination, linked
validation, Core construction, resolved-owner authentication, transforms, and
observation teardown. Deep and wide cases run on 256 KiB threads. With type and
kind depth 32,768 and generated-origin depth 16,384, the linked witness costs
311,361 units and fits the existing production default. The predecessor
depth-96 and width-32,767 Core witnesses retain their dimensions and limits.

The source-order correction at `8c11cd3` moves allocation into one fallibly
reserved cross-family preparation pass. It neither clones a second binder nor
adds a resource limit. Its only new kind-bearing fields are resolution-owned
transient preparation carriers recorded in the closed inventory.

## Tampering and negative evidence

Private mutation matrices reject each retained relationship independently:

- canonical variable identity, spelling, origin, kind, module, and source
  order;
- nominal owner, parameter order, constructor family, payload, kind, and hidden
  or opaque closure;
- checked and summary interface, global, implementation, method, requirement,
  and selected-evidence mirrors;
- imported fact identity, route, visibility, parameter, application, and kind;
- resolved-global owner facts that are empty, missing, extra, duplicated,
  reordered, wrong-owner, wrong-position, nominal, interface-only, or left
  unconsumed;
- Core abstraction, outer scheme, application arity, argument order, kind,
  occurrence, scope, provenance, and immediate recursive owner;
- generated binder inconsistency, duplication, capture, shadowing, or escape;
  and
- identity and literal-folding transform results, each rebuilt independently
  from the original validated program.

The named tamper anchors are
`exhaustive_summary_orders_indexes_aliases_and_owners_fail_before_local_checking`,
`exhaustive_public_and_hidden_summary_carriers_fail_before_local_checking`, and
`fused_constructor_scheme_authentication_rejects_every_independent_type_obligation`
in `src/resolve/module_tests.rs`;
`rejects_every_task8_kinded_linked_diamond_carrier_before_core`,
`rejects_every_surviving_linked_nominal_and_constructor_mirror_before_core`,
`linked_registry_rejects_every_resolved_global_parameter_row_mutation_before_core`,
and `linked_registry_canonical_malformation_precedes_a_later_row_mismatch` in
`src/evidence_validation.rs`;
`linked_core_rejects_each_independent_registry_row_structure_mutation`,
`linked_core_rejects_coherent_resolved_binder_owner_swap`,
`linked_core_rejects_coherent_resolved_binder_reorder`,
`linked_core_sequential_bind_cannot_claim_a_resolved_global_row`,
`linked_core_rejects_each_independent_generated_binder_mutation`, and
`linked_core_preserves_registry_graph_binder_and_abstraction_precedence` in
`src/core/validate.rs`; and
`rejects_registry_identity_order_spelling_and_source_forgery` in
[`tests/core_validation.rs`](../../../tests/core_validation.rs).
`kind_inventory_is_closed` and `transient_kind_site_owners_are_source_anchored`
in [`tests/architecture.rs`](../../../tests/architecture.rs) make the carrier
inventory itself fail closed.

The corresponding positive matrix accepts exact resolved owner/order matching,
complete generated alpha-renaming, both transforms followed by fresh
validation, erasure, and evaluation.
`linked_core_accepts_capture_free_generated_alpha_renaming` in
`src/core/validate.rs` is the explicit positive generated-identity witness.

## Production and maintenance sites

| Boundary | Principal production owners |
| --- | --- |
| syntax and projection | `src/parser/grammar.rs`, `src/parser/project.rs`, `src/parser/mod.rs`, `src/surface.rs` |
| identities, canonical application, and resolved kind gate | `src/resolve.rs`, `src/resolved.rs`, `src/kind.rs`, `src/types.rs` |
| inference, matching, selection, and checking | `src/elaborate.rs`, `src/interface.rs`, `src/pattern.rs` |
| body-free and linked facts | `src/evidence.rs`, `src/evidence_validation.rs`, `src/driver.rs` |
| kind-aware Core construction, validation, and transforms | `src/core/dialect.rs`, `src/core/validate.rs`, `src/core/transform.rs`, `src/core/type_ops.rs` |
| iterative observation and structural inspection | `src/eval/value.rs`, `src/eval/machine.rs` |

Primary maintenance suites are `parser`, `interfaces_syntax`, `resolution`,
`kinds`, `kind_modules`, `polymorphism`, `interfaces`, `implementations`,
`interface_modules`, `interface_validation`, `evidence_validation`,
`core_validation`, `type_properties`, `architecture`, `diagnostics`,
`resources`, `corpus`, `spec_examples`, `module_cli`, and `library_imports`.

## Verification status

The Task 11 migration checkpoint passes 37 polymorphism tests, 49 resolution
tests at that checkpoint, nine corpus tests, 48 predecessor specification
examples, 32 interface tests, three kind-module tests, and 56 Core-validation
tests, followed by the complete all-target and all-feature workspace suite,
Clippy with warnings denied, `cargo xtask verify`, Markdown lint, formatting,
and diff hygiene.

The source-order correction adds two resolution tests, so the focused resolver
suite now contains 51 passing tests. Its independent semantic/authority and
Rust/resource/atomicity reviews both pass with `gpt-5.6-sol` at `xhigh`
reasoning. The 42 focused resolver resource and teardown tests, 21 architecture
tests, 56 Core-validation tests, the linked behavioral regression, all-target
Clippy, formatting, and diff hygiene pass without a limit change.

Task 12 began with 57 executable specification tests. After the resolver
correction, 49 behavior and predecessor-document cases passed and the remaining
eight failed only because the normative kind examples and rule fragments had
not yet been reconciled. The reconciled specification now passes all 57 tests.
Independent architecture-decision, normative-authority, and evidence-lifecycle
reviews pass without findings, each with `gpt-5.6-sol` at `xhigh` reasoning.
`cargo xtask verify`, Markdown lint, relative-link checks, formatting, and diff
hygiene pass at the Task 12 checkpoint. At that point, Task 13 still had to
record the fresh complete workspace inventory, final review corrections, exact
verification, and lifecycle cleanup.

Task 13's implementation/Core/resource review passes without findings. Its
normative review found and corrected one stale lexical claim that named type
applications were saturated. Its evidence/lifecycle review restored the
canonical interface parameter identity in `IOTA` and retained the width-1,000
malformed-Core and depth-32,000 teardown witnesses above. Both correction
reviews then pass without remaining findings. All three reviewers used
`gpt-5.6-sol` at `xhigh` reasoning.

The fresh all-target inventory contains 1,422 tests: 642 library tests, ten
`ash` binary tests, 769 integration tests, and one `xtask` test. Formatting,
all-target and all-feature checking, all 1,422 tests, Clippy with warnings
denied, the exact test inventory, `cargo xtask verify`, Markdown lint,
relative-link checks, and diff hygiene pass on the retained tree. This report
is the final evidence record for the bounded increment; transition-artifact
cleanup does not close or tag the complete `lib-ash` milestone.

## Intentional exclusions and remaining pressure

This increment does not add method-local source type parameters,
multi-parameter interfaces, functional dependencies, associated outputs,
defaults, specialization, type lambdas, kind inference, kind polymorphism,
higher-order unification, source `forall`, explicit term type application,
higher-rank source values, runtime kind values, compatibility syntax, packages,
manifests, persistent summaries, compiled artifacts, or separate linking.

Later work may use the fixed kind environments, canonical applications, stable
identities, body-free facts, and authenticated linked boundary. It requires its
own semantic authority and evidence. The complete `lib-ash` milestone remains
open and untagged.
