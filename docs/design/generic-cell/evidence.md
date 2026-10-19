# Generic cell checkpoint evidence

This record maps accepted [CP-0023](../../proposals/CP-0023-scoped-generic-cells.md)
observations to product tests. The [current specification](../../../spec/README.md)
defines Ash; this record supplies evidence and no additional permission.
[TASK-0048](../../tasks/TASK-0048-generic-cell-integrated-verification.md)
owns this matrix. TASK-0049's fresh complete workspace gate and original
compound acceptance remain pending. Coordinator acceptance here is bounded to
TASK-0048 focused readiness.

## Observation boundaries

The retained TASK-0046 dependency component was accepted at code `3f72e9c`.
TASK-0047's runtime component was observed at `8d5b3c1`, with the independent
architecture inventory repair at `ac72d18` and receipt head `9cfd39a9`.
Their task records retain exact commands, input records, log hashes and bounded
transfers. TASK-0048 changes test bodies in compiler source files, so those
historical runs do not imply identical compiler fingerprints or a fresh gate.
The frozen TASK-0048 receipt below binds these observations to exact inputs.

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

## Variant traceability

The generic opaque-wrapper and selected-evidence witnesses for N02/N07 are
`cell_n02_n07_imported_evidence_dependencies_survive_wrappers_and_crossings`;
its imported pack/unpack and Read/invoke routes pair independent old snapshots
with hidden owner captures. Direct wrapper/live-reader variants are named
`cell_n02_access_wrappers_and_live_reader_results_cannot_leave_their_owner`.
N06's imported P04 later-read companion is
`cell_p04_imported_read_helper_preserves_two_call_snapshots`; its direct pair is
`cell_p04_snapshot_stays_independent_after_dependent_replacement`.
N07's indexed-only carrier witness is
`cell_n07_indexed_operation_metadata_alone_crosses_with_its_owner`.
P06's ordinary rigid-owner boundary is
`cell_p06_distinct_rigid_owners_do_not_unify_at_an_ordinary_branch`: different
owners fail Typing/type.mismatch while same-owner aliases admit. N09's missing
exact evidence fails Typing/constraint.unsatisfied; counterfeit family fails
Resolution/resolve.unknown-type.

C02's initializer capture/discard observation is
`generic_cell_c02_initializer_discard_never_publishes_the_unacquired_owner`.
Its outside-pending-resume unsafe completion and ordinary owned discard are
separated in `generic_cell_completion_keeps_structural_discard_obligations`.
Running cleanup has its own source control,
`generic_cell_running_cleanup_cannot_be_abandoned_by_an_outer_handler`, with
source Typing/effect.discard-unsafe and causal discard labels. The independent
Core capture-authority control is
`generic_cell_actual_core_rejects_discard_of_running_cleanup`: it checks the
actual mutated completion operation and refuses Unsafe/Cleanup. It does not
claim complete altered-arena validation or execute an orphaned malformed graph.

C05's captured capacity and fresh-key control is
`generic_cell_captured_capacity_preserves_latest_root_and_fresh_reuse`.
Repeated large/shared cyclic reads are named
`generic_cell_repeated_large_cyclic_reads_share_the_exact_heap_root`.
Deep function-root modes and common deep captured-control walker tests are
separate observations. Adding the discard mode initially inflated the shared
test closure and overflowed mode-zero acquisition before discard on 64 KiB;
a test-only helper extraction removed that caller-frame aggregation. The final
probe performs fresh acquisition, capture and owned discard at the same stack
limit, without warming paths, cloning the deep root or changing production
runtime behavior.

## Frozen focused receipt

The retaining code/test pin is unsigned
`b785e5605569492103a64ffb9e2a3b5de64ded88`, tree
`70577492c6ed4297a40a2451f7e18639d0386ac4`.
Its 1,769 path/mode/content records have canonical SHA-256
`0136ae86db4d585bec0023defebe3d893eb3b7048b20b50aca92c5bc99201b85`;
the saved manifest file SHA-256 is
`f0adaee2028949a9c699fe6e64845e75c20dfe94e0b011bddf50e9baa267bfe9`.
All source, tests, fixtures, manifest/lockfile and configuration stayed fixed
during their applicable checks. Rust/Cargo 1.97.1, rustfmt 1.9.0 and Clippy
0.1.97 were reconfirmed with their executable/configuration hashes. All commands
used `CARGO_BUILD_JOBS=1 RUSTC_WRAPPER=` and the existing target cache.

The library/resource/view/architecture/rank-1 observations ran at initial
unsigned candidate `b3445f51b6aafb6b3e7a866a438763104dd595f8`, tree
`6c71acf7605281d03ae32e72b5bb36bad7bf79ad`, with 1,769 records SHA-256
`518ead7bdc00be1ceb255495ff1a0dba63be92cbae5189c81beda7d8cfbb8905`.
The only subsequent repair changed optional evidence-collector paths in
`tests/source_resource_execution.rs`: generated Rust/images live under src,
whereas Cargo inputs live at its parent and the build log has its own accessor.
The failed collector run stopped before host execution; its failed receipt and
partial artifacts remain separate and supply no C06 result. Exact comparison
retains all 1,768 other records, including every production/compiler source,
configuration, fixture and exercised input for those five unaffected targets.
Those five receipts transfer within that scope only. Fresh fmt/strict Clippy
used the complete repaired records before the administrative commit; fresh
native and rustdoc observations ran at the retaining pin. No prior native
observation transfers across the collector failure.

Working manifests, receipts and raw logs remain outside the target cache in
`/tmp/task0048-launch/frozen/`. The following command/result/input/log digest
summary is durable here; it is focused evidence and not the complete workspace
gate. Nested child-test summaries are not counted twice.

### fmt

```sh
cargo fmt --check
```

Passed.
Log SHA-256:
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

### clippy

```sh
cargo clippy -p ash --all-targets --all-features --locked -- -D warnings
```

Passed, warnings denied.
Log SHA-256:
`e95307c7c88b6e2caacdfcd9265dc9529c7d8693a8a9195654deb75b342f928f`.

### lib

```sh
cargo test --lib --locked -- --show-output
```

1,937 passed.
Log SHA-256:
`c0aec9f25203c06128b6fa5940cef903998adeb2a7536d662d21d22997ca4b0c`.

### resource

```sh
cargo test --test resource_scope_typing --test resource_scope_modules \
    --test resource_scope_core --test resource_scope_runtime --test \
    cleanup_abandonment --test cleanup_interactions --test \
    cleanup_partial_acquisition --locked
```

173 passed: typing 105, modules 16, Core 2, runtime 32; cleanup 11 + 6 + 1.
Log SHA-256:
`a8ee06292022533d8ef28d46c1ed1b1eca821bf00766d64478de2302c13c3dfa`.

### views

```sh
cargo test --test copying_sqlite_source --locked generic_cell_n11 -- \
    --nocapture
```

One test passed, covering three prohibited-view shapes and two valid companions.
Log SHA-256:
`46dffc6926368098a1d488e898b45d76fd0a69b27e536b4717023822818e587b`.

### architecture

```sh
cargo test --test architecture --locked
```

All 47 passed.
Log SHA-256:
`ca36e55e43a9345db58b86cb69fc71fa0f069c36710b654cd758175af7763877`.

### rank1

```sh
cargo test --test core_validation --locked \
    rejects_nested_forall_as_an_outer_instantiation_argument -- --exact
```

One shared Core rank-1 control passed.
Log SHA-256:
`a58c7f3549bca70be6da5fc0015d9e9649fc46c7d50061a3d3b90feff0595349`.

### native

```sh
cargo test --test source_resource_execution --locked \
    generic_cell_c06_stored_native_access_reads_after_quarantine_but_\
cannot_restore_use \
    -- --exact --nocapture
```

One paired test passed: two actual generated native hosts. Native evidence
collection used `ASH_OWNER_EVIDENCE_DIR` set to
`/tmp/task0048-launch/frozen/native-artifacts`.
Log SHA-256:
`c8e13cfe35c1580ccf668ad49f09896b33740c228ccc70c1b6fb03d75a37e689`.

### rustdoc

```sh
cargo doc -p ash --no-deps --all-features --locked
```

Passed, warnings denied via RUSTDOCFLAGS="-D warnings".
Log SHA-256:
`97ae32712a1310a707d514947709536684a412a09645072f372de7bd3da626b7`.

## Real native input and output binding

Both generated hosts embed runtime fingerprint
`b8c62ad3ad13fab49c6cd4197f7d14d395eb0628f187e0bd8829bc57d58e1fce`.
The operator parsed all 32 hexadecimal bytes from generated Rust and compared
them with the recorded matching compiler identity. Each case retains and hashes
14 inputs: serialized complete case preimage, entry/owner/native source, native
object/archive, linked executable, generated Rust, image/expected facts, Cargo
manifest/lockfile/toolchain and native build log. Four post-execution outputs
(native trace, stdout, stderr and exact optional exit status) are independently
hashed. The readback additionally records ELF linker metadata and actual dynamic
library paths/hashes: 21 retained files per case. Its manifest SHA-256 is
`a525773b3239dce15847f996211244737dd5092b9adf05ba3e766293d7d499f9`.

Actual tools are GCC 15.2.0, GNU ar 2.46, Rust 1.97.1 and LLD 22.1.6, on
x86_64 Linux 7.0.0-38 with glibc 2.43. The six C-tool/resolved frontend/linker
hashes and two bundled Rust-linker hashes were checked against actual files;
ELF comments independently identify GCC/Rust/LLD in both executables. Rust's
nine executable/configuration pins match the preceding component receipts.
The native compiler/link commands, generated Cargo inputs and library hashes
are retained in the input manifests; no implicit current prebuilt binary is
substituted for these generated hosts.

Permitted stored-handle case:

- Complete case key: `dc1f33c3e4a855e278d49937874768d9dbd94e60ff3f73cc38cf7553f51d93ba`.
- Linked host SHA-256:
  `4c6d7c41ecd760ea18aed37d0736bee3796ba560ee33623fb1bbacbc9a7ef423`.
- Generated Rust SHA-256:
  `c2974e0fbe198bce87d236bc8635596f3c502c898f078b9a433fe5b730aa7b95`.
- Native trace SHA-256:
  `e0f3b1a06f22abab1345f01e4887bd4305696ddb400bb9a01558dbb60dec4097`.

Denied provider/State-access case:

- Complete case key: `56f23e25e528ea04d70720dc1df24f5fd17118b555b8abd433d96e44ac0ad57d`.
- Linked host SHA-256:
  `693886bc9e610ed298d6d42adc2403da7c374327bafbd044897bf06bfa9e4015`.
- Generated Rust SHA-256:
  `07212db8956db643273c012a3b395ef1ec5270245443f750f031b7e4b8894240`.
- Native trace SHA-256:
  `5affeb71e2330f5fb7270df6086a581ac7fadff3a73aa6c30351273008c76905`.

The permitted case returns `Completed(42, RetainedError(()))`, exits zero and
ends with parent byte 99. The denied case reaches the second successful ordinary
Cell.read and closes C, then attempts `Owner.borrow recovered`: existing
provider/State authority rejects before native entry, exits one, emits the
internal-control-state message and leaves parent byte zero. This observes
provider/State access denial on the path toward native use; it does not claim a
native borrow call occurred. Both actual C traces acquire parent64/child4,
retain child4, release child4, then release parent64 exactly once. C's close
neither consumes A nor removes B-to-A native protection. These are real native
observations, separate from injected teardown failures.

## Review, acceptance and remainder

Independent reviewer `/root/task0046_reviewer` cleared the complete code and
technical evidence at the retaining pin, including actual raw log hashes,
precise five-stage input transfer and native post-execution readback.
Coordinator `/root` accepted TASK-0048 focused readiness on 2026-10-19.
Developer/Cargo operator remains `/root/task0046_developer`, dispatched
`gpt-6.1-sol`, `medium`. Receipt prose and explicit existing-scope
specification wording receive manual
Markdown/link/authority review and exact executed source/test/config retention
checks. The static semantics now states the accepted rule explicitly: R is a
logical owner, Cell lifetime is exactly its resource scope, and backing storage
cannot extend live access/reader escape or defer required completion.

Original TASK-0046/0047/0048/0049 compound criteria and all-31-case checkpoint
acceptance remain open. TASK-0049 must run the fresh default complete
seven-stage
`cargo xtask verify` without reuse at the retained handoff, preserve durable
stage/input/tool/log summaries, then perform its acceptance and authorized
lifecycle cleanup. Complete legacy/ffi regressions are required there; this
focused run does not relabel unselected native targets as freshly executed.
DN-0054 remains separate and byte-identical. No push, PR/Main integration or
worktree/cache retirement is part of this handoff.
