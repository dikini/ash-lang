# Generic cell checkpoint evidence

This record maps accepted [CP-0023](../../proposals/CP-0023-scoped-generic-cells.md)
observations to product tests. The [current specification](../../../spec/README.md)
defines Ash; this record supplies evidence and no additional permission.
[TASK-0048](../../tasks/TASK-0048-generic-cell-integrated-verification.md)
owns this matrix. TASK-0049's fresh complete workspace gate and coordinator
acceptance remain pending. A working observation is not a frozen receipt.

## Observation boundaries

The retained TASK-0046 dependency component was accepted at code `3f72e9c`.
TASK-0047's runtime component was observed at `8d5b3c1`, with the independent
architecture inventory repair at `ac72d18` and receipt head `9cfd39a9`.
Their task records retain exact commands, input records, log hashes and bounded
transfers. TASK-0048 changes test bodies in compiler source files, so those
historical runs do not imply identical compiler fingerprints or a fresh gate.
The final TASK-0048 receipt will bind the observations below to frozen inputs.

The public runtime fixtures use `compile_path`, independent linked Core
admission and actual execution. `generic_runtime_observation` checks the value,
write count, unique acquired keys and exactly one matching release per key.
The generic dependency-negative fixtures require source/compiled parity,
`Typing`, `type.resource-escape`, actual causal expressions and acquisition/
capture/call labels. Ordinary restriction fixtures assert their own public
phase and reason. Deliberately corrupted Core is never executed after rejection.

## Positive cases

Runtime names below are in
[resource_scope_runtime.rs](../../../tests/resource_scope_runtime.rs).

### CELL-P01

`generic_cell_p01_fixed_payload_shapes_share_aliases`: Int replacement 42,
Bool true, tuple (42, true), nominal projection 42.
`generic_cell_p01_initializer_runs_once_before_body_publication`: (42, 1),
initializer once.

### CELL-P02

`generic_cell_p02_snapshots_and_p03_outer_access_have_actual_values`: (41, 42)
and escaped snapshot 41.

### CELL-P03

Same test: recovered enclosing access returns 7 after inner completion.

### CELL-P04

`generic_cell_p04_p05_p13_imported_snapshots_and_recursive_owners_execute`:
direct/imported earlier independent snapshot escapes and returns 7. Later
dependent-read negatives remain N06.

### CELL-P05

Same test: direct/imported same-site recursion returns 9, two distinct live
keys, one release per acquisition.

### CELL-P06

`generic_cell_p06_local_imported_facade_and_same_owner_branch_agree`: both
branch choices through local/imported/facade routes return 42 with one slot
and one write. Generic distinct-owner branch refusal is separately ordinary
typing.

### CELL-P07

`generic_cell_p07_exact_handler_interception_and_forwarding_execute`:
overridden read 99, intercepted write leaves 41, forwarded write yields 42
once; nonforwarded self-capturing function replacement leaves independent 7
with zero builtin writes.

### CELL-P08

`generic_cell_p08_actual_local_reply_and_independent_escape_execute`:
dependent local reply 42, independent escaping reply 7.

### CELL-P09

`generic_cell_p09_independent_and_enclosing_payload_crossings_execute`:
permitted independent/enclosing crossings return 42/7.

### CELL-P10

`generic_cell_p10_cyclic_immutable_payload_keeps_finite_prefix`: finite prefix
2. Owning machine test also checks repeated reads preserve the same Location
and constant shallow-copy cost for 8,192 shared cyclic nodes.

### CELL-P11

`generic_cell_p11_repeated_monomorphic_reads_and_legacy_nesting_execute`:
repeated fixed-function results and mixed legacy/generic behavior return 42.
Indexed effectful function payload companion invokes its saved outer owner and
returns 7.

### CELL-P12

`generic_cell_p12_other_handler_mutation_survives_original_write_interception`:
Tick's separate mutation yields 99, one builtin write; intercepted 42 is not
published.

### CELL-P13

`generic_cell_p04_p05_p13_imported_snapshots_and_recursive_owners_execute`:
escaping independent handler snapshot 7.
`generic_cell_p13_reply_and_later_stored_function_have_distinct_actual_values`:
(7, 42), one actual mutation. N12 checks the later dependent read cannot
escape.

## Negative cases

Unless stated otherwise, names are in
[resource_scope_typing.rs](../../../tests/resource_scope_typing.rs).

### CELL-N01

`cell_n01_generic_ordinary_errors_precede_dependency_admission`: wrong
initializer/type and write use Typing `type.mismatch` / `type.argument`; arity
and row-as-Type use Resolution `resolve.type-kind`; higher-kinded payload uses
Kind `kind.argument`.

### CELL-N02

`cell_n02_access_wrappers_and_live_reader_results_cannot_leave_their_owner`,
`cell_n02_hidden_access_closures_and_n05_unsafe_payload_joins_reject`,
imported evidence/opaque-wrapper companions: source ResourceEscape for
direct/wrapped access and identity-free hidden captures; independent snapshots
admit.

### CELL-N03

`cell_n03_self_retention_and_n04_younger_cycle_reject_at_write`:
self-capturing replacement fails at first invalid retention; later clearing
cannot repair it. P07's intercepted/discarded replacement admits.

### CELL-N04

Same test plus
`cell_n04_wrappers_and_selected_fields_keep_only_actual_payload_dependencies`:
genuine A-to-B-to-A cycle, with and without later clearing; opaque selected
fields and imported capture factory retain the hidden dependency. Independent
projection companions admit.

### CELL-N05

`cell_n05_every_possible_target_must_admit_the_replacement`,
`cell_n05_resumed_stack_does_not_extend_an_older_slots_birth_enclosure`,
unsafe payload joins: younger dependency fails without requiring a cycle;
every possible target/alternative is checked.

### CELL-N06

`cell_p08_actual_handler_reply_dependencies_pair_with_n06_escape` and P04
snapshot/later-read pairs: dependent actual reply or current contents cannot
escape; earlier independent reply/snapshot can.

### CELL-N07

`cell_n07_outer_write_interceptor_rejects_crossing_but_inner_interceptor_discards`:
outer exact write interceptor cannot receive B-dependent payload across B;
inner interceptor can discard it.
`cell_n02_n07_imported_evidence_dependencies_survive_wrappers_and_crossings`
and indexed metadata-only tests preserve ordinary per-owner crossing.

### CELL-N08

`cell_n08_generic_initializer_and_payload_precede_fresh_binders`: fresh c/R
unavailable in initializer/T, Resolution unknown-name/type. Preceding nominal
R and term c companion passes public compile, independent Core and execution
42.

### CELL-N09

`cell_n09_generic_calls_need_exact_evidence_and_counterfeit_family_cannot_acquire`:
missing exact evidence and counterfeit family refuse.
`cell_n09_generic_provider_is_sealed_through_direct_and_facade_imports` in
resource_scope_modules covers impl/with, direct/facade, public Resolution
`resolve.sealed-provider`.

### CELL-N10

`cell_n10_generic_read_is_monomorphic_before_admission`: Typing
`type.argument` for incompatible uses.
`cell_n10_nested_schemes_are_not_source_payload_types`:
direct/tuple/higher-rank T attempts fail public syntax `parse.expected-form`;
independent Core nested-Forall controls remain separate.

### CELL-N11

`cell_n11_native_state_and_continuation_payloads_keep_ordinary_restrictions`,
wrapped-continuation companion, and generic declared-view test in
copying_sqlite_source: direct/tuple/nominal State/view use source Typing
`type.argument` with existing controlled-state restriction; continuation
capture uses `effect.resume-capture`. Same-library Int/`Wrapped<Int>`
view-fixture companions execute 42.

### CELL-N12

`cell_p13_reply_snapshot_and_n12_later_builtin_read_keep_distinct_dependencies`:
later builtin read retains A and fails at A's close; independent handler reply
escapes and returns 7.

## Control, validation and failure cases

### CELL-C01

`generic_cell_c01_capture_resume_moves_the_latest_function_root`: (41, 42),
one acquisition, two writes, one release. Machine full-request controls
distinguish complete T/family, two live same-T donor keys, stale/fresh keys
and actual foreign-arena Request provenance before access/mutation. No
external Value transport or global nonce is claimed.

### CELL-C02

`generic_cell_c02_owned_discard_keeps_both_cells_live_for_dependent_cleanup`:
cleanup reads enclosing cell before inner release, once. Initializer-discard
companion preserves earlier side effect 1 and publishes no new cell. Outside
completion and running cleanup have distinct source unsafe-discard controls;
actual independent Core running-completion mutation returns Unsafe/Cleanup.

### CELL-C03

Original/copied/identity/folded/restored Core re-enters independent admission.
Imported snapshot/recursive/handler image values are 7/9/7; stateful P12/P13
transformed values are 99/(7,42). Full ordered R,T handle/request/provider
mutations and origin/operation/row controls reject ordinarily. Possible-target
and hidden-capture changes retain ordinary arrow/provider/row validity and
fail ResourceEscape; safe-target companions return 42. Body-free summary
coherence and linked-body reconstruction are separate controls.

### CELL-C04

Source module publication, recursive summaries, Core
construction/validation/restoration and runtime acquisition/write have
measured exact/one-short/two-fresh retry ledgers. Refusal publishes no
permission/root or replacement. Strict operand-effect witness preserves side
12 and target 41 on refusal, versus full (42,12); earlier operand effects are
not rolled back.

### CELL-C05

Capacity counts active and captured owners; fresh keys remain distinct after
release. Shared 8,192-node cyclic roots retain Location without deep read
copies. Admitted origin depth 130 and sole environment depth 32,000 cover
normal/replacement/internal failure and actual owned capture/discard at
unchanged 64 KiB, with live/captured accounting and exactly one release.
Common control-walker depth tests remain separate.

### CELL-C06

`generic_cell_c06_stored_native_access_reads_after_quarantine_but_cannot_restore_use`
in source_resource_execution uses real generated native hosts. Stored access
read before/after quarantine and C close are permitted; later Owner.borrow
refuses before entry. Permitted result Completed(42, RetainedError(())) ends
parent byte99; denied host exits1/internal control state and byte0. Both
traces acquire parent64/child4, retain child4, release child4 then parent64
exactly once. Compiler/native/linker/artifact pins accompany final frozen
observation. Legacy/ffi State/data/crossing/retention/blocked
teardown/destruction suites remain mandatory at TASK49's fresh full gate.

## Independent authority witnesses

[Core validation tests](../../../src/core/validate.rs) distinguish ordinary
metadata validity from dependency proof. In
`generic_cell_full_payload_and_ordered_owner_vectors_are_authenticated`,
changed-T and swapped-R/T handle vectors return `NodeType`; changed-T and
swapped-R/T Request vectors return `EffectRow`; the corresponding selected
provider vectors return `NodeType`. The original Request is explicitly the
canonical generic Ops family. Its owned argument is fixed at position zero;
there is no writable owned-position field to corrupt.
`cell_core_rejects_detached_brand_provider_and_source_authority` and
`cell_core_rejects_a_request_with_the_wrong_operation_fact` now run for both
legacy and generic families. Existing row and ordinary-fact mutations remain
separate from hidden stored-value dependencies.

`generic_cell_possible_target_owners_rebuild_after_transforms` changes only an
identity-free closure's hidden scalar binding to the actual A access, updating
that immediate binder type. A Bool parameter chooses safe B first and A second;
main calls both alternatives. Actual Core reconstruction rejects ResourceEscape
when A is possible. The otherwise identical B/B companion admits and executes
42. This is not rejection of a mismatched operation/provider/arrow/row.
`generic_cell_linked_hidden_retention_is_reconstructed_after_transforms` and
`generic_cell_core_rebuilds_escape_crossing_and_later_read_dependencies` cover
hidden self-retention, crossing and later-read dependencies after transforms.

The [capture unit](../../../src/core/capture.rs)
`generic_cell_body_free_write_summary_authenticates_contents_graph_and_return`
starts from an actual checked public `put<R,T>` export, retaining a stored-value
graph and the indexed type of its authentic Cell.write call. Its unchanged
binder/scheme/origin/capture fact compares equal. Erased/replaced graph or erased
returned-target relationships compare unequal. This comparison is duplicate
import-route coherence, not a second Core admission API.
The reachable [resolver control](../../../src/resolve/module_tests.rs)
`generic_cell_duplicate_import_routes_reject_erased_contents_capture_fact`
uses both direct and facade routes to that same binder. Genuine routes admit;
erasing only facade capture rejects Resolution/InternalState with the alternate
global checked-fact mismatch. Linked actual-Core hidden-body refusal remains a
separate proof and never trusts a forged body-free summary.

`generic_cell_stateful_handler_results_survive_actual_core_transforms` executes
original, copied identity and folded inputs at P07 read99/intercept41/forward42,
P12 Tick99 and P13 (7,42). Tick uses real literal arithmetic 90+9; its folded
program must contain fewer Primitive nodes before independent admission and
execution. `generic_cell_exact_handler_owner_ports_survive_independent_core_transforms`
executes imported distinct/equal owner routing and discarded replacement cases
at 7. `generic_cell_imported_flow_images_rebuild_with_exact_short_and_retry_work`
restores snapshot7, recursion9, handler7, intercepted function7, scalar99/41/42,
Tick99 and reply mutation(7,42). Tick's image is encoded from independently
revalidated optimized Core. Images reconstruct proofs after original inputs
have been dropped.

N10 additionally retains the universal independent Core control
`rejects_nested_forall_as_an_outer_instantiation_argument` in
[core_validation.rs](../../../tests/core_validation.rs); this is the shared
rank-1 boundary, not a claim that source syntax can denote a nested scheme.
N11's additional concrete names are
`cell_n11_wrapped_continuations_keep_the_ordinary_capture_refusal` and
`generic_cell_n11_declared_views_cannot_be_payloads_or_hidden_in_wrappers`.
The latter resides in
[copying_sqlite_source.rs](../../../tests/copying_sqlite_source.rs) and checks
valid same-library Int and nominal-wrapped Int companions before all three
prohibited-view shapes.

The owning C01 malformed-request test is
`generic_cell_requests_reject_wrong_type_live_donor_stale_and_family`.
C05's sole deep root is checked by
`generic_cell_admitted_function_origin_and_deep_environment_dispose_on_small_stack`:
its 32,000-deep environment head has strong count one before acquisition;
capture moves the root and live/captured accounting remains one. Actual owned
discard returns live/captured to zero, preserves next key one, and observes
Acquired/Discard/Released/ClauseReturned in that order. The original 64 KiB
stack and admitted origin bound 130 are unchanged.

## Exact work boundaries

These probes measure each boundary on fresh state, refuse with one fewer unit,
and perform two fresh sufficient retries. Costs are measured by the owning
ledger rather than borrowed from a different phase. The frozen library receipt
executes the assertions; its shown output retains the reported costs.

- Source inference: `generic_cell_elaboration_work_has_exact_budgets_and_fresh_retry`
  uses the elaborator's `TypeWorkBudget`; active acquisitions return to zero
  after success and refusal. `generic_cell_helper_publication_refusal_keeps_evidence_empty_and_retries_exactly`
  separately checks no partial lexical evidence escapes refusal.
- Checked module and recursive summary publication:
  `generic_cell_imported_flow_publication_is_exact_and_retryable` measures
  `check_module_with_budget` for imported snapshot, recursion and handler
  fixtures. One-short returns no checked module; both fresh exact runs consume
  the measured allowance. Constraint/usefulness ledgers retain their existing
  defaults and are not claimed as separate exact measurements.
- Core construction:
  `generic_cell_core_builder_reconstruction_is_exact_and_fresh_retryable`
  uses the existing transform builder ledger, separately from elaboration.
  Identity/fold reconstruction measure 331 units on the checked Bool fixture;
  330 remaining units return `Build(TypeWorkExceeded)` and no output. Two fresh
  sufficient reconstructions independently revalidate and execute 42.
- Independent Core validation:
  `generic_cell_core_dependency_work_is_exact_and_retryable` and
  `generic_cell_imported_snapshot_recursive_and_handler_core_work_is_retryable`
  measure the complete validation counter, including dependency proof, for
  original/identity/folded inputs. One-short reports `ValidationReason::Resource`;
  exact fresh runs admit. The direct recursive public probe retains its
  unchanged 256,335-unit allowance and observes 244,447 units used.
- Image restoration:
  `generic_cell_imported_flow_images_rebuild_with_exact_short_and_retry_work`
  measures one `TypeWorkBudget` across decode, expected-native-fact admission
  and independently checked Core restoration. One-short publishes no restored
  program; exact fresh retries rebuild it. Snapshot/recursion/handler and
  stateful interceptor/Tick/reply-mutation fixtures execute their named values.
- Runtime acquisition:
  `generic_cell_acquisition_work_refusal_is_atomic_and_retryable` measures
  instantiation work and tests every shorter prefix. Acquisition work refusal
  preserves root/frame publication, live count, next key and trace; exact fresh
  runs publish one owner.
- Runtime replacement:
  `generic_cell_write_preflight_is_atomic_paid_and_retryable` measures Access
  work, including integer magnitude copying and request/result trace retention,
  tests every shorter prefix and retries exactly twice. Refusal preserves old
  root/key/counts/trace. `generic_cell_write_refusal_retains_prior_strict_operand_effects`
  separately measures the real machine path: full work 194 returns (42,12),
  allowance 137 refuses final Access after two earlier writes, leaving side12
  and target41 with no target Request/result publication.

Internal teardown failure after a completed replacement remains distinct:
`generic_cell_replaced_function_root_reports_internal_disposal_failure_after_commit`
checks Teardown/EnvironmentDisposal and incomplete execution after publication.
It is not evidence of preparation rollback or a new source cleanup guarantee.

## Ledger and receipt status

This working map is not acceptance. TASK-0048's frozen command receipt, exact
input/tool/native manifests and independent verdict remain to be appended.
TASK-0049 must execute the fresh full workspace checkpoint before original
compound criteria or all 31 cases are accepted.
