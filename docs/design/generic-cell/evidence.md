# Generic cell checkpoint evidence

This record maps the accepted generic cell transition to product tests.
The [current specification](../../../spec/README.md)
defines Ash; this record supplies evidence and no additional permission.
The original 2026-10-19 local checkpoint was verified at
`7e80df3e66a6d3074b86f29b7582cadb6696a563`: all seven default stages
executed freshly, with zero reused stages. The 140 parent test harnesses report
4,112 passes, zero failures and one optional native calibration study ignored.
The then-recorded default-feature native pair embeds runtime fingerprint
`6270711a6b9492367ecff76a0b1612a1b21f475b44282d9618eabbd08598fcf9`.
The final receipt below supersedes earlier component-only readiness.
The checkpoint is integrated into local `main`; the 2026-10-20 receipt below
records the fresh integration gate and retained result. Earlier checkpoint,
acceptance and cleanup observations remain scoped to their recorded commits.
The transition artifacts were retired after checkpoint acceptance.

The sections from “Observation boundaries” through “Retained cleanup readback
and local closure” record the 2026-10-19 checkpoint. Their Main authorization,
retention and default-feature native statements describe that earlier boundary.
The later local Main receipt follows those historical observations.

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

Original/copied/identity/folded compiler Core re-enters independent admission.
At this historical checkpoint, restored images also repeated that admission;
the current generated-host boundary is recorded in
[AD-0013](../../decisions/AD-0013-generated-native-bridges-and-program-builds.md).
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
binder/scheme/origin/capture fact compares equal. Erased/replaced graph or
erased
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
execution.
`generic_cell_exact_handler_owner_ports_survive_independent_core_transforms`
executes imported distinct/equal owner routing and discarded replacement cases
at 7.
`generic_cell_imported_flow_images_rebuild_with_exact_short_and_retry_work`
restores snapshot7, recursion9, handler7, intercepted function7, scalar99/41/42,
Tick99 and reply mutation(7,42). Tick's image is encoded from independently
revalidated optimized Core. At that checkpoint, images reconstructed proofs
after original inputs had been dropped; current generated hosts reconstruct the
compiler-validated representation without repeating the proof.

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
  and Core restoration under the then-current validation policy. One-short
  publishes no restored program; exact fresh retries rebuild it. Snapshot/recursion/handler and
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

## Historical TASK-0048 focused receipt

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

## Historical TASK-0048 native binding

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

## Historical TASK-0048 review and remainder

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

The following complete checkpoint receipt supersedes this historical focused
remainder. Earlier receipts remain bounded to their own declared inputs,
commands and fingerprints. They do not imply byte equality with the final
checkpoint. The final gate executes all preserved legacy/native targets.

## Fresh complete checkpoint gate

The sole build operator ran the default complete gate without reuse or
stage filters on frozen inputs. No product file changed during the run.

```sh
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= \
ASH_SQLITE_STATIC_ARCHIVE=/tmp/task0049-sqlite-prerequisite/libsqlite3.a \
cargo xtask verify \
    --input /home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/\
bin/cargo \
    --input /home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/\
bin/clippy-driver \
    --input /home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/\
bin/rustc \
    --input /home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/\
bin/rustfmt \
    --input /home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/\
lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld/ld.lld \
    --input /home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/\
lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld \
    --input /lib64/ld-linux-x86-64.so.2 \
    --input /tmp/task0049-sqlite-prerequisite/libsqlite3.a \
    --input /tmp/task0049-sqlite-prerequisite/sqlite-amalgamation-3460100.zip \
    --input /tmp/task0049-sqlite-prerequisite/sqlite3.c \
    --input /tmp/task0049-sqlite-prerequisite/sqlite3.h \
    --input /tmp/task0049-sqlite-prerequisite/sqlite3.o \
    --input /usr/bin/ar \
    --input /usr/bin/cc \
    --input /usr/bin/nm \
    --input /usr/bin/readelf \
    --input /usr/bin/x86_64-linux-gnu-ar \
    --input /usr/bin/x86_64-linux-gnu-as \
    --input /usr/bin/x86_64-linux-gnu-gcc-15 \
    --input /usr/bin/x86_64-linux-gnu-ld.bfd \
    --input /usr/bin/x86_64-linux-gnu-nm \
    --input /usr/bin/x86_64-linux-gnu-readelf \
    --input /usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2 \
    --input /usr/lib/x86_64-linux-gnu/libc.so.6 \
    --input /usr/lib/x86_64-linux-gnu/libgcc_s.so.1 \
    --input /usr/lib/x86_64-linux-gnu/libm.so.6 \
    --input /usr/lib/x86_64-linux-gnu/libsqlite3.so.0 \
    --input /usr/lib/x86_64-linux-gnu/libsqlite3.so.0.8.6 \
    --input /usr/libexec/gcc/x86_64-linux-gnu/15/cc1 \
    --input /usr/libexec/gcc/x86_64-linux-gnu/15/collect2
```

- Code/document input commit: `7e80df3e66a6d3074b86f29b7582cadb6696a563`.
- Tree: `dd26e7d5a2218cdf374c626af7759e558b8105ef`.
- Repository inventory (1,769 files) SHA-256: `d470d374f0540649718f04bef22ae85ed4bd0bb3f78a2e6a54a7ace24cef231b`.
- Operator receipt SHA-256: `2be060b3fb77cd959d4cfd07b3675927fd3375c3c7c3a327c652899c5c7a9501`.
- Complete stdout SHA-256: `854a405ea45e256339e72d6d93ebd83f863cb8ff8345199ea4fe8a7a19029b13`.

The following stage commands ran freshly; each terminal status was zero.

### Complete gate: format

```sh
cargo fmt --all --check
```

Elapsed seconds: `9.692987282`.
Log SHA-256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
Stage receipt SHA-256:
`093556a372577f74904633497ab66a664d9ba0270611db50cd90cd1b8552b2f2`.

### Complete gate: metadata

```sh
cargo metadata --format-version 1 --locked --no-deps
```

Elapsed seconds: `0.016850596`.
Log SHA-256: `6b5d88f0feb5de4b5f95039b3ffcf291c493b3d92b663658264b8cb2ac8c37a7`.
Stage receipt SHA-256:
`005d5bed7658e1791414bd06ed3bfd217fc265fc17ba00e6b57cb07bad8958e9`.

### Complete gate: check

```sh
cargo check --workspace --all-targets --locked
```

Elapsed seconds: `0.31929546`.
Log SHA-256: `d7dae192715495fa89ccbe279af3efb9792c1dae1768228e369035e68a1df673`.
Stage receipt SHA-256:
`ce7365f1796821a0117dfa6a9c7d84b811dca1e1f7b38fc055fb28f13c0feb9d`.

### Complete gate: build

```sh
cargo build --workspace --lib --bins --examples --locked
```

Elapsed seconds: `0.129419723`.
Log SHA-256: `4cf86278c1e6d659943a46a3d7e3da429ac15be90f0f17742e24ef85228e7d3e`.
Stage receipt SHA-256:
`6094585140cb82d2322223f397c33d2e286871bc7f42ab777867c631c2cdfa8c`.

### Complete gate: clippy

```sh
cargo clippy --workspace --all-targets --all-features --locked -- -D warnings
```

Elapsed seconds: `0.360834044`.
Log SHA-256: `d7dae192715495fa89ccbe279af3efb9792c1dae1768228e369035e68a1df673`.
Stage receipt SHA-256:
`0609cc04db6cb91eccf99bcdf936fda4acf5d5a5bed9abbf37df33feb3722f45`.

### Complete gate: test

```sh
cargo test --workspace --all-targets --all-features --locked
```

Elapsed seconds: `888.624643464`.
Log SHA-256: `1d5114e7f1019ab520bd170db1e5877d95828c3069c8ddd1237e1463186c71d4`.
Stage receipt SHA-256:
`f7aa97a8a25dc1bef7fe099e10e77ed78e23d89eb6816835829fe436c4d6333c`.

### Complete gate: documentation

```sh
RUSTDOCFLAGS='-D warnings' cargo doc --workspace --no-deps --locked
```

Elapsed seconds: `18.103189801`.
Log SHA-256: `299e1b45676ebe450573328fac701b5c9ee2a996dcfb4eda0a852562a137d043`.
Stage receipt SHA-256:
`ffb24eb3e626388e421bccc8956892c81aaaa5c64464e8d0fae9eaacb69ec0d2`.

### Executed suites

Parent harness totals exclude nested child-process summaries:

{"failed": 0, "filtered_out": 0, "ignored": 1, "measured": 0, "passed": 4112}

- `unittests src/lib.rs`:
  1939 passed; 0 ignored.
- `unittests src/main.rs`:
  20 passed; 0 ignored.
- `tests/architecture.rs`:
  47 passed; 0 ignored.
- `tests/bindings.rs`:
  10 passed; 0 ignored.
- `tests/bytes_strings.rs`:
  6 passed; 0 ignored.
- `tests/check_ffi.rs`:
  11 passed; 0 ignored.
- `tests/cleanup_abandonment.rs`:
  11 passed; 0 ignored.
- `tests/cleanup_interactions.rs`:
  6 passed; 0 ignored.
- `tests/cleanup_partial_acquisition.rs`:
  1 passed; 0 ignored.
- `tests/cleanup_reporting.rs`:
  8 passed; 0 ignored.
- `tests/cleanup_syntax.rs`:
  7 passed; 0 ignored.
- `tests/cleanup_typing.rs`:
  14 passed; 0 ignored.
- `tests/cli.rs`:
  17 passed; 0 ignored.
- `tests/cli_build.rs`:
  6 passed; 0 ignored.
- `tests/compiled_program.rs`:
  3 passed; 0 ignored.
- `tests/compiler_work_reporting.rs`:
  5 passed; 0 ignored.
- `tests/copying_sqlite_source.rs`:
  29 passed; 0 ignored.
- `tests/core_validation.rs`:
  67 passed; 0 ignored.
- `tests/corpus.rs`:
  13 passed; 0 ignored.
- `tests/data_and_adts.rs`:
  32 passed; 0 ignored.
- `tests/diagnostic_catalogues.rs`:
  3 passed; 0 ignored.
- `tests/diagnostic_input.rs`:
  9 passed; 0 ignored.
- `tests/diagnostic_json.rs`:
  1 passed; 0 ignored.
- `tests/diagnostic_options.rs`:
  7 passed; 0 ignored.
- `tests/diagnostic_precedence.rs`:
  13 passed; 0 ignored.
- `tests/diagnostic_presentation.rs`:
  9 passed; 0 ignored.
- `tests/diagnostic_rendering.rs`:
  5 passed; 0 ignored.
- `tests/diagnostic_reporting.rs`:
  3 passed; 0 ignored.
- `tests/diagnostics.rs`:
  83 passed; 0 ignored.
- `tests/effect_core.rs`:
  6 passed; 0 ignored.
- `tests/effect_diagnostics.rs`:
  23 passed; 0 ignored.
- `tests/effect_modules.rs`:
  13 passed; 0 ignored.
- `tests/effect_rows.rs`:
  13 passed; 0 ignored.
- `tests/effect_runtime.rs`:
  27 passed; 0 ignored.
- `tests/effect_typing.rs`:
  30 passed; 0 ignored.
- `tests/effects_syntax.rs`:
  5 passed; 0 ignored.
- `tests/file_diagnostic_dispatch.rs`:
  7 passed; 0 ignored.
- `tests/foreign_codec_failures.rs`:
  10 passed; 0 ignored.
- `tests/foreign_common_module.rs`:
  5 passed; 0 ignored.
- `tests/foreign_module_admission.rs`:
  23 passed; 0 ignored.
- `tests/foreign_native_program_preparation.rs`:
  6 passed; 0 ignored.
- `tests/foreign_source_admission.rs`:
  12 passed; 0 ignored.
- `tests/foreign_source_contracts.rs`:
  11 passed; 0 ignored.
- `tests/foreign_source_owner_admission.rs`:
  8 passed; 0 ignored.
- `tests/foreign_source_owner_contracts.rs`:
  4 passed; 0 ignored.
- `tests/foreign_source_syntax.rs`:
  8 passed; 0 ignored.
- `tests/functions.rs`:
  19 passed; 0 ignored.
- `tests/hooks_core.rs`:
  12 passed; 0 ignored.
- `tests/hooks_runtime.rs`:
  15 passed; 0 ignored.
- `tests/hooks_syntax.rs`:
  7 passed; 0 ignored.
- `tests/hooks_typing.rs`:
  25 passed; 0 ignored.
- `tests/implementations.rs`:
  80 passed; 0 ignored.
- `tests/integer.rs`:
  8 passed; 0 ignored.
- `tests/interface_corpus.rs`:
  11 passed; 0 ignored.
- `tests/interface_diagnostics.rs`:
  9 passed; 0 ignored.
- `tests/interface_generic_summary.rs`:
  4 passed; 0 ignored.
- `tests/interface_identity_diamond.rs`:
  2 passed; 0 ignored.
- `tests/interface_modules.rs`:
  24 passed; 0 ignored.
- `tests/interface_resources.rs`:
  6 passed; 0 ignored.
- `tests/interface_selection.rs`:
  40 passed; 0 ignored.
- `tests/interface_validation.rs`:
  2 passed; 0 ignored.
- `tests/interfaces.rs`:
  44 passed; 0 ignored.
- `tests/interfaces_syntax.rs`:
  30 passed; 0 ignored.
- `tests/kind_modules.rs`:
  3 passed; 0 ignored.
- `tests/kind_resources.rs`:
  1 passed; 0 ignored.
- `tests/kinds.rs`:
  27 passed; 0 ignored.
- `tests/kinds_syntax.rs`:
  15 passed; 0 ignored.
- `tests/lexer.rs`:
  25 passed; 0 ignored.
- `tests/library_imports.rs`:
  17 passed; 0 ignored.
- `tests/local_newtypes.rs`:
  20 passed; 0 ignored.
- `tests/local_newtypes_syntax.rs`:
  4 passed; 0 ignored.
- `tests/method_parameter_resources.rs`:
  4 passed; 0 ignored.
- `tests/modular_closure.rs`:
  4 passed; 0 ignored.
- `tests/module_cli.rs`:
  17 passed; 0 ignored.
- `tests/module_elaboration.rs`:
  8 passed; 0 ignored.
- `tests/module_elaboration_nominals.rs`:
  8 passed; 0 ignored.
- `tests/module_entry.rs`:
  14 passed; 0 ignored.
- `tests/module_loading.rs`:
  24 passed; 0 ignored.
- `tests/module_newtypes.rs`:
  21 passed; 0 ignored.
- `tests/module_resolution.rs`:
  11 passed; 0 ignored.
- `tests/module_visibility.rs`:
  4 passed; 0 ignored.
- `tests/modules_syntax.rs`:
  20 passed; 0 ignored.
- `tests/native_buffer_core.rs`:
  3 passed; 0 ignored.
- `tests/native_buffer_imports.rs`:
  9 passed; 0 ignored.
- `tests/native_buffer_interactions.rs`:
  8 passed; 0 ignored.
- `tests/native_buffer_modules.rs`:
  6 passed; 0 ignored.
- `tests/native_buffer_runtime.rs`:
  9 passed; 0 ignored.
- `tests/native_buffer_source.rs`:
  13 passed; 0 ignored.
- `tests/native_buffer_syntax.rs`:
  4 passed; 0 ignored.
- `tests/native_buffer_typing.rs`:
  12 passed; 0 ignored.
- `tests/newtype_resources.rs`:
  1 passed; 0 ignored.
- `tests/packed_core.rs`:
  9 passed; 0 ignored.
- `tests/parser.rs`:
  50 passed; 0 ignored.
- `tests/polymorphism.rs`:
  43 passed; 0 ignored.
- `tests/primitive_vertical.rs`:
  12 passed; 0 ignored.
- `tests/program_build.rs`:
  5 passed; 0 ignored.
- `tests/program_build_native.rs`:
  3 passed; 0 ignored.
- `tests/provenance.rs`:
  4 passed; 0 ignored.
- `tests/provider_arena_allocation.rs`:
  7 passed; 0 ignored.
- `tests/provider_arena_source.rs`:
  4 passed; 0 ignored.
- `tests/provider_control_source.rs`:
  22 passed; 0 ignored.
- `tests/provider_owner_rows.rs`:
  9 passed; 0 ignored.
- `tests/provider_retention_source.rs`:
  3 passed; 0 ignored.
- `tests/provider_sqlite_control.rs`:
  2 passed; 0 ignored.
- `tests/provider_sqlite_copying.rs`:
  8 passed; 0 ignored.
- `tests/provider_sqlite_sessions.rs`:
  8 passed; 0 ignored.
- `tests/provider_sqlite_source.rs`:
  10 passed; 0 ignored.
- `tests/recursion.rs`:
  10 passed; 0 ignored.
- `tests/resolution.rs`:
  60 passed; 0 ignored.
- `tests/resource_calibration_native.rs`:
  0 passed; 1 ignored.
- `tests/resource_calibration_observer.rs`:
  2 passed; 0 ignored.
- `tests/resource_provider_resolution.rs`:
  15 passed; 0 ignored.
- `tests/resource_provider_syntax.rs`:
  9 passed; 0 ignored.
- `tests/resource_scope_core.rs`:
  2 passed; 0 ignored.
- `tests/resource_scope_modules.rs`:
  16 passed; 0 ignored.
- `tests/resource_scope_runtime.rs`:
  32 passed; 0 ignored.
- `tests/resource_scope_syntax.rs`:
  5 passed; 0 ignored.
- `tests/resource_scope_typing.rs`:
  105 passed; 0 ignored.
- `tests/runtime_diagnostics.rs`:
  10 passed; 0 ignored.
- `tests/scoped_evidence.rs`:
  2 passed; 0 ignored.
- `tests/scoped_evidence_interactions.rs`:
  53 passed; 0 ignored.
- `tests/scoped_evidence_syntax.rs`:
  6 passed; 0 ignored.
- `tests/semantics.rs`:
  13 passed; 0 ignored.
- `tests/source_arena_execution.rs`:
  5 passed; 0 ignored.
- `tests/source_diagnostics.rs`:
  10 passed; 0 ignored.
- `tests/source_resource_acquired_only.rs`:
  5 passed; 0 ignored.
- `tests/source_resource_execution.rs`:
  79 passed; 0 ignored.
- `tests/source_resource_resolution.rs`:
  18 passed; 0 ignored.
- `tests/source_resource_syntax.rs`:
  2 passed; 0 ignored.
- `tests/spec_examples.rs`:
  79 passed; 0 ignored.
- `tests/sqlite_library.rs`:
  35 passed; 0 ignored.
- `tests/string_literals.rs`:
  7 passed; 0 ignored.
- `unittests src/lib.rs`:
  49 passed; 0 ignored.
- `tests/arena.rs`:
  10 passed; 0 ignored.
- `tests/sqlite_text.rs`:
  11 passed; 0 ignored.
- `unittests examples/arena.rs`:
  0 passed; 0 ignored.
- `unittests examples/arena_typed.rs`:
  0 passed; 0 ignored.
- `unittests examples/sqlite_session.rs`:
  0 passed; 0 ignored.
- `unittests src/main.rs`:
  0 passed; 0 ignored.
- `tests/verify.rs`:
  17 passed; 0 ignored.

Raw working records remain outside the target cache under
`/tmp/task0049-complete-with-sqlite/`. These digests and complete command/result
summaries retain the checkpoint evidence independently of cache lifetime.

Independent review and coordinator acceptance are recorded under
Checkpoint acceptance and retained-input boundary.
Executed source/test/config/fixture equality after receipt prose and cleanup
is verified by the retained readbacks below.

The 140 parent harnesses report 4,112 passes, zero failures and one ignored
optional native calibration study. Nine child-process summaries are excluded
from these counts. The ignored study is not a CP-0023 case. No test filter
was requested. All 30 external byte/mode/link records and repository/tool
records are equal before and after the gate. Every stage records canonical
environment SHA-256:
`0b1ff2ae01f528844f5e7087aa4aecd899607fc446024dcbac03285edb433b9f`.

## Current native quarantine observation

Frozen code: `7e80df3e66a6d3074b86f29b7582cadb6696a563`.
Both independently generated hosts embed runtime fingerprint
`6270711a6b9492367ecff76a0b1612a1b21f475b44282d9618eabbd08598fcf9`.
The positive host returns `Completed(42, RetainedError(()))`, status zero;
the paired provider/State-access refusal reports inconsistent control state,
status one, before native borrow entry. Their exact traces differ only in
parent-final-byte 99 versus 0, with child release before parent release.
The historical TASK-0048 b8 fingerprint below is a distinct earlier run.

The complete post-execution native readback SHA-256 is
`badefb0bf8c0f7688bf09fcb228146133c71096814572fd9170687ca959b1069`.
Its two case preimages, keys and every retained file were independently
verified, including input tools, embedded fingerprint and dynamic libraries.

The static SQLite archive environment is consumed only by the SQLite workload
helper and is excluded from compiler/runtime fingerprint configuration. The
current C06 source, tools and its own native inputs remain unchanged across
that prerequisite setup; the complete gate has a broader external/environment
fingerprint. This collector command uses default features. The full workspace
test stage uses all features and independently exercises C06; no generated
binary equality is asserted across those feature configurations.

The focused collector ran once with one build job and an empty Rust wrapper.
`ASH_OWNER_EVIDENCE_DIR=/tmp/task0049-repaired/native-artifacts` retained
the two actual hosts. Exact test selection:

```sh
cargo test --test source_resource_execution --locked \
    generic_cell_c06_stored_native_access_reads_after_quarantine_but_cannot_\
restore_use \
    -- --exact --nocapture
```

Native log SHA-256:
`5fbcd1014cb0c5ca62ba2c04b7f115108281d25a84e00d632b466302b08f4a23`.
Operator receipt SHA-256:
`cc18918a6eabb8d748f9b59690fff90436b2b23a8cfd7590f8c8551b368ec33a`.

### Native status 0

Case preimage/key SHA-256:
`61f61b2def775c537c4f2912ab714845b950493754e6eb9aea122df19e860a5d`.

- `Cargo.lock` SHA-256:
  `1095bf7bb381414fc9d23a876bb0ad88cef52d46525843c1df1e333c51470850`.
- `Cargo.toml` SHA-256:
  `84bdf1f41873e4551ccad8c0f223de9657385e699c5b8aa0495652628189514b`.
- `case-inputs.json` SHA-256:
  `61f61b2def775c537c4f2912ab714845b950493754e6eb9aea122df19e860a5d`.
- `dynamic-libraries.txt` SHA-256:
  `11b46e4ef20b79ac8112c988c763ade2b35703948969307c68852bdbd7863400`.
- `elf-linker-comment.txt` SHA-256:
  `e3c7ac576e038de4ad0b8204de2b388acb47be48db95cbd2e16c5155de77bebb`.
- `entry.ash` SHA-256:
  `354bf3b61e252cca7b5868745e2cbf3a50d9c1e82660a7d318d54b38a21e9d14`.
- `exit-code` SHA-256:
  `e67403f811c9e0307b56d6067ee62452c96101087926773b09f24f8f923fb7db`.
- `expected-facts.bin` SHA-256:
  `7c5ab6e601d40c1d68e6656c4676527508823806e8acd2c84a693aa36ef82c6b`.
- `generated.rs` SHA-256:
  `d092f0fd6414befe7984561b4264804d94303a73fdecf3a44422c86388fcb6cb`.
- `inputs.json` SHA-256:
  `30c5c45cfc69114e41cedccf9f1886a20b9124f7de8d5f3f062754f58bd10039`.
- `native-build.log` SHA-256:
  `4ac61bf23d7788c3486918565bee94709c4219cdb4f59c5e4cf1b597ee3f7b96`.
- `native-trace` SHA-256:
  `e0f3b1a06f22abab1345f01e4887bd4305696ddb400bb9a01558dbb60dec4097`.
- `native_library` SHA-256:
  `2e6941bfb030d03daa3467b3578a65f1eb5be761f3fa03d60a0f22a7e1ca62da`.
- `native_owner.c` SHA-256:
  `f2517bde5d012ed946e3b4042f6b5e9ae9860469980b108a6ac06406c8e52a51`.
- `native_owner.o` SHA-256:
  `086d76fd2a7b54c08281379fbc8d06a3d26baca550d90375fd7c8110dc8e32aa`.
- `owner.ash` SHA-256:
  `542326baaba3391f26c5cdf0521e52c7a1699769cfb9c8b29f8ad54e94ecc4af`.
- `program` SHA-256:
  `b23cdb57380f475348724081cf3391afaee86dd3246f9effca0cb23426dcb63e`.
- `program-image.bin` SHA-256:
  `b9a38669c118e1da20084dd817fbd7159dab3607c363d28dfc34d686011bb5df`.
- `rust-toolchain.toml` SHA-256:
  `cdb9bea833b62d4c26fbba417000b2929746d667ba25ad4eee40dfa61aa75a89`.
- `stderr` SHA-256:
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `stdout` SHA-256:
  `73dca124c41d123ccd3e37f2f4c5820c0abb454fbcd2b8c6b3c5f9603e9962a8`.

### Native status 1

Case preimage/key SHA-256:
`88326c26ecb599bdb550e7a128d67c05a192ef554956d4cacc6fdbbd04a268d8`.

- `Cargo.lock` SHA-256:
  `397f81dea463bbe72c8c59894091ab4ccd1051fa59b2a3c3657e71ba917e8c77`.
- `Cargo.toml` SHA-256:
  `6a508ad9155fe00747c613088d74e3e74584522539e27bde5045255cec67388e`.
- `case-inputs.json` SHA-256:
  `88326c26ecb599bdb550e7a128d67c05a192ef554956d4cacc6fdbbd04a268d8`.
- `dynamic-libraries.txt` SHA-256:
  `d9c76fd57ba3c39a2fc9572d65e47b0ec5b6c7414a459782e5c9e6f2d923c79f`.
- `elf-linker-comment.txt` SHA-256:
  `e3c7ac576e038de4ad0b8204de2b388acb47be48db95cbd2e16c5155de77bebb`.
- `entry.ash` SHA-256:
  `1b4cf2a9cb40759052efc31cbfd13b508b465fdfbeafbdaf659bab24039ed920`.
- `exit-code` SHA-256:
  `d6e36ebf7a67e41cba8650a93a22f4e1fe88e12cf4381d2b15ca5f6adacbdb62`.
- `expected-facts.bin` SHA-256:
  `c75198c99240d831ccb13b67025761c128644f28352060d108573ec97eff8feb`.
- `generated.rs` SHA-256:
  `64e52ca2d99e1a1164da0d762dd7523626213b60c6c5d07938d12497db924e56`.
- `inputs.json` SHA-256:
  `ac336c5d97c6e0abaeda90b65f0800a8a51808128f17e859eefb5391d23fa340`.
- `native-build.log` SHA-256:
  `f3a73f4afe421440025e4a95a62749327ea37749c9c44b405b05c2832959df1d`.
- `native-trace` SHA-256:
  `5affeb71e2330f5fb7270df6086a581ac7fadff3a73aa6c30351273008c76905`.
- `native_library` SHA-256:
  `1ee545410eb01bd34eafa3b69e340c47d9e64db3c4261557a5f120252c4f1d91`.
- `native_owner.c` SHA-256:
  `f2517bde5d012ed946e3b4042f6b5e9ae9860469980b108a6ac06406c8e52a51`.
- `native_owner.o` SHA-256:
  `fe3ed686aad963a248f7756a135cae7d5a4f24685a74555db1b545eb0a7bf99f`.
- `owner.ash` SHA-256:
  `542326baaba3391f26c5cdf0521e52c7a1699769cfb9c8b29f8ad54e94ecc4af`.
- `program` SHA-256:
  `395cb2e55de32690c71a9e80084539233810353a36d447f977ed3a85223bcc51`.
- `program-image.bin` SHA-256:
  `4ad660df6f60ab693450ca0c8d436f1d7aa122daf8a0e1564f63211c515d349d`.
- `rust-toolchain.toml` SHA-256:
  `cdb9bea833b62d4c26fbba417000b2929746d667ba25ad4eee40dfa61aa75a89`.
- `stderr` SHA-256:
  `54be4403d05b844a8381816fade3a8cb1b68e97c4fae0ca0453255a8815aae1e`.
- `stdout` SHA-256:
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## Complete-gate repair history

Three earlier complete-gate attempts failed and remain separate from the final
checkpoint. None of these failed runs supplies a complete checkpoint pass.

### Initial attempt

Input commit: `e3cb981f27d15f84c866a352259e2285b2541bb4`.
Terminal gate status: `1`; input/tool equality held.
Complete stdout SHA-256:
`eee194de50027bc3ada11c8f2262b0b4f503912b5d37fa8b7666c4722da12ffe`.
Operator receipt SHA-256:
`64e1e732773df9b74d1cfc985d025ce01f41554e8f117cb226b5f5b53d79bf09`.

The SQLite native test helper unwrapped optional CARGO_TARGET_DIR before host
preparation. Its target had 14 passes and 15 panics. Nine sites across three
native integration-test files now preserve an override or use the existing
repository target/ffi-native-hosts default.

### Cache-repaired attempt

Input commit: `9f35eaf310fb0dd5199cb9bea9d98404ade9aa25`.
Terminal gate status: `1`; input/tool equality held.
Complete stdout SHA-256:
`e2258fa2c4ff694f36788fe3ce1784419cf171b73be58ff934d13c7f627de00d`.
Operator receipt SHA-256:
`441fbb6c19a4939a184ab21925e80d80ef966145f28000287b0b05df6880560e`.

The unchanged 8,000-member recursion fixture exhausted source type work during
generic identity discovery. The test-cache repair itself passed the complete
affected native targets before this later failure.

### Discovery diagnosis and repair

The source scan began with 264,097 units used out of 327,680 and 48,009
completed Core nodes. Further generic-type discovery exhausted the same
ledger. After the source-only cost repair, the focused unchanged fixture
reached a second refusal in independent Pure Core discovery at its unchanged
983,040-unit limit. These are distinct phases, not one shared allowance.

The retained implementation pays a base and every canonical identity-store
entry before source discovery, including materialized, lexical and opaque
abstract nominal kinds and canonical effects. Absent generic identities avoid
the redundant full scan. Existing generic origins and capture-summary
publication remain intact. Independent Pure Core recomputes its own census
only after ordinary registry, row, binder, node, scope and anchor checks, and
only for final Pure input without contextual/provider/external or separate
abstract authority. Effect and contextual/provider discovery remain unchanged.
No source safety bit is transferred to Core.

The exact/one-short/two-fresh census test checks all four stores and defining
identity rather than spelling. Raw missing-family Core still rejects NodeType.
The original 8,000 members, 256 KiB stack and source/Core work limits are
unchanged; the complete ten-test recursion target passes. Connected controls
pass 47 generic unit probes, four contextual tests and 155 resource tests.
Strict workspace Clippy, format and the complete 47-test architecture audit
pass. The fresh seven-stage receipt supplies the final checkpoint result.

### Missing static SQLite prerequisite

At unchanged `7e80df3e66a6d3074b86f29b7582cadb6696a563`, the third
complete attempt passed the preceding targets and reached the SQLite library
suite: 34 passed; the genuine static workload refused its missing mandatory
`ASH_SQLITE_STATIC_ARCHIVE`. Documentation had prescribed this operator input;
it was omitted from that attempt. No product or assertion repair was needed.
The failed run is not relabelled as a complete checkpoint pass.

Failed stdout SHA-256:
`e61e9f26c601fe6fb8e2ceda64b690234ef7e7dcf45642b8156283a9d2afde96`.
Failed operator receipt SHA-256:
`43c8dc2b2f0fc7ca605cc1f8aa65973ab20173513e5dbab32115d87325e2736d`.

The prescribed official SQLite 3.46.1 ZIP, C and header hashes were verified;
the header equals the vendored header. The sources were copied read-only from
a retained input bundle, then rebuilt with current `cc -O2 -fPIC -c` and
`ar crs`, preserving default compile options. The genuine archive is
1,397,878 bytes, SHA-256:
`7c2b4dc4aa149543e60252b5fffcb62088398470a09885cebb5e3120459c0617`.

Build receipt SHA-256:
`b6065cff7ec1f9b87a87ac0e3184cb64b2d20c9edafb60f0b6a4947921665d52`.
The actual all-feature static copying workload passed, checking eight
implementation symbols in archive and executable, no SQLite DT_NEEDED, and
the complete copying result. Its log SHA-256:
`a44b870f802ab498e43655442a30a30a97b080fe9abaaccf4c8f7f338342109a`.

The final retry declares the archive path in the environment and all archive,
ZIP, C, header, object, selected C/Rust tools/linkers and shared SQLite/runtime
library bytes as explicit inputs. This preserves the default complete seven
stages; no reuse or filtered stage is requested. Source, tests, configuration
and the current 627 native observation are unchanged.

## Checkpoint tool and configuration identities

Rust/Cargo 1.97.1, rustfmt 1.9.0, Clippy 0.1.97, Linux x86_64,
GCC 15.2.0 and the selected C/Rust linkers were checked at the frozen pin.
Every command keeps `CARGO_BUILD_JOBS=1 RUSTC_WRAPPER=`. No resource,
stack or capacity limit changes are part of the repairs.

### tools-config.json

Record SHA-256:
`6eabfd0f0a4bd13a0f03eea9b35ac5c1cf1ab6ad3790bf1e3ff2c54bee92a662`.

- `rustc executable`:
  `d3a664c970a9fd8361b64194861bebc1ae37b9054e5ee3400dc1c9e691797eea`.
- `cargo executable`:
  `828980723df339d62434390e9fb8ef8831036583343ae2316b7ab5646b5c1953`.
- `rustfmt executable`:
  `30de9e1efcd8f8fe7750e00d0c45ff8f4c480608ef1be5baf9ab6f1b4556e8f8`.
- `clippy-driver executable`:
  `e8fa6ad666c353e4c9248fc67074cf160ff2a5dbd97debd20416b81d7f917373`.
- `/home/dikini/.cargo/config.toml`:
  `13ed130670278614272c1fca1af627d4e427b8d306cd530a96f0d7555dbcd6a5`.
- `.cargo/config.toml`:
  `2eb887744ac35113f513a449e09d637cf4ae0e08e8361bd7b3401e41e37051f9`.

### native-tool-pins.json

Record SHA-256:
`0baaf3a5c89d8168f300ae3bd0d80b490887fdc47ab8aeedaa95c439eaf41445`.

- `cc`:
  `b5f1b773a7c733738352000c92a077dc5852a1a2fc6d836b1e411be1e9ec5f88`.
- `ar`:
  `531473816bf553e863df5aab14c8177c72b732cf80c51dcf0fa990a50125041c`.
- `ld`:
  `97f48d93b8b076a92d2809ec29dcb17f0f37c8827358f832255e2ed22fef6075`.
- `cc-selected-ld`:
  `97f48d93b8b076a92d2809ec29dcb17f0f37c8827358f832255e2ed22fef6075`.
- `cc-selected-cc1`:
  `30510b346885152c4fce41d2b501751c95d3690b1c34eaa04ebb970e70eae620`.
- `cc-selected-collect2`:
  `8ab5d946ba2c948e5ea5c91e25a104439302e0599a521785770d10690c565437`.

### rust-linker-pins.json

Record SHA-256:
`d89b8b4a1c7dca7eacacc80ec5867d9e20d230120427f580b1f6572701fe5bd2`.

- `rust-lld`:
  `38a9f28404309892f9c9afe02fa4979a0d9e8bc866979cde09f5bb7ec17e5721`.
- `gcc-ld/ld.lld`:
  `514ad5e5087dee69b173ab8a0bc0dfc717be3a2b2a47fcb4f36f50afe4d779c7`.

### Repository configuration inputs

- `Cargo.lock`:
  `26be4499e4330e8146d024cfbf6950f6e711edc5909c9a700ec0f2ed58749e08`.
- `Cargo.toml`:
  `2d1a3d056418f5feb2e36d3ff99924e30f6a9136900b7aa2bb73ead902a1395c`.
- `rust-toolchain.toml`:
  `cdb9bea833b62d4c26fbba417000b2929746d667ba25ad4eee40dfa61aa75a89`.

## Explicit external checkpoint inputs

The complete gate declares all 30 paths below with `--input`, including the
genuine static archive and source bundle, selected compiler/archive/symbol/ELF
tools, compiler backends/linkers, shared SQLite and runtime libraries.
The archive environment is
`ASH_SQLITE_STATIC_ARCHIVE=/tmp/task0049-sqlite-prerequisite/libsqlite3.a`.
All default seven stages run; `--input` adds byte identities, not stage filters.

- `/home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/bin/cargo`:
  SHA-256 `828980723df339d62434390e9fb8ef8831036583343ae2316b7ab5646b5c1953`.
- `/home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/bin/clippy-driver`:
  SHA-256 `e8fa6ad666c353e4c9248fc67074cf160ff2a5dbd97debd20416b81d7f917373`.
- `/home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/bin/rustc`:
  SHA-256 `d3a664c970a9fd8361b64194861bebc1ae37b9054e5ee3400dc1c9e691797eea`.
- `/home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/bin/rustfmt`:
  SHA-256 `30de9e1efcd8f8fe7750e00d0c45ff8f4c480608ef1be5baf9ab6f1b4556e8f8`.
- `/home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld/ld.lld`:
  SHA-256 `514ad5e5087dee69b173ab8a0bc0dfc717be3a2b2a47fcb4f36f50afe4d779c7`.
- `/home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld`:
  SHA-256 `38a9f28404309892f9c9afe02fa4979a0d9e8bc866979cde09f5bb7ec17e5721`.
- `/lib64/ld-linux-x86-64.so.2`:
  SHA-256 `bda779ea9e9ad234f60315477d7cfd0bdde861cd8ddd9df8cdaf62f18c4cec14`.
- `/tmp/task0049-sqlite-prerequisite/libsqlite3.a`:
  SHA-256 `7c2b4dc4aa149543e60252b5fffcb62088398470a09885cebb5e3120459c0617`.
- `/tmp/task0049-sqlite-prerequisite/sqlite-amalgamation-3460100.zip`:
  SHA-256 `77823cb110929c2bcb0f5d48e4833b5c59a8a6e40cdea3936b99e199dbbe5784`.
- `/tmp/task0049-sqlite-prerequisite/sqlite3.c`:
  SHA-256 `6c35bc5f7f85eac9c49928bacbb02bb694b547aabf69197e058cca245ad80e83`.
- `/tmp/task0049-sqlite-prerequisite/sqlite3.h`:
  SHA-256 `89b62c671c5964e137409ce034941b7b05a3af2c9875aba41f47f9483d0c2515`.
- `/tmp/task0049-sqlite-prerequisite/sqlite3.o`:
  SHA-256 `ccd7e4bedda7aa4530b482098e56c8ac3d24cbd0368d5d98804523d2aea04cad`.
- `/usr/bin/ar`:
  SHA-256 `531473816bf553e863df5aab14c8177c72b732cf80c51dcf0fa990a50125041c`.
- `/usr/bin/cc`:
  SHA-256 `b5f1b773a7c733738352000c92a077dc5852a1a2fc6d836b1e411be1e9ec5f88`.
- `/usr/bin/nm`:
  SHA-256 `f04262bf48192a7cbb78a17ca49ae03f8930b0372bd0115576f957b2e2a57a01`.
- `/usr/bin/readelf`:
  SHA-256 `c857339616bbbfa5eba32733e22365048903fbaf6ed2126b897dd138bcb741fc`.
- `/usr/bin/x86_64-linux-gnu-ar`:
  SHA-256 `531473816bf553e863df5aab14c8177c72b732cf80c51dcf0fa990a50125041c`.
- `/usr/bin/x86_64-linux-gnu-as`:
  SHA-256 `4e5fcaa3cdc160173cb5cfe7aa35dc39d7aa1f06ba8d75b8d923bbae5473991b`.
- `/usr/bin/x86_64-linux-gnu-gcc-15`:
  SHA-256 `b5f1b773a7c733738352000c92a077dc5852a1a2fc6d836b1e411be1e9ec5f88`.
- `/usr/bin/x86_64-linux-gnu-ld.bfd`:
  SHA-256 `97f48d93b8b076a92d2809ec29dcb17f0f37c8827358f832255e2ed22fef6075`.
- `/usr/bin/x86_64-linux-gnu-nm`:
  SHA-256 `f04262bf48192a7cbb78a17ca49ae03f8930b0372bd0115576f957b2e2a57a01`.
- `/usr/bin/x86_64-linux-gnu-readelf`:
  SHA-256 `c857339616bbbfa5eba32733e22365048903fbaf6ed2126b897dd138bcb741fc`.
- `/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2`:
  SHA-256 `bda779ea9e9ad234f60315477d7cfd0bdde861cd8ddd9df8cdaf62f18c4cec14`.
- `/usr/lib/x86_64-linux-gnu/libc.so.6`:
  SHA-256 `85e64f97e348786a8fb4d9f3d52fec289e2fb86bba20f0731dfe61990525e0f7`.
- `/usr/lib/x86_64-linux-gnu/libgcc_s.so.1`:
  SHA-256 `9d339ecb409578d6a5d587e6c537a8f9589b8a13fefba30d167433a4b5758bee`.
- `/usr/lib/x86_64-linux-gnu/libm.so.6`:
  SHA-256 `1c488db6f4fe8cecb72456bc018de000b7a9b539c2994864b0416b5e8371b3d8`.
- `/usr/lib/x86_64-linux-gnu/libsqlite3.so.0`:
  SHA-256 `4633a4be13fdf05cb0f859e04fb06077a1fe30a90e405721a23873bd1f3d88a8`.
- `/usr/lib/x86_64-linux-gnu/libsqlite3.so.0.8.6`:
  SHA-256 `4633a4be13fdf05cb0f859e04fb06077a1fe30a90e405721a23873bd1f3d88a8`.
- `/usr/libexec/gcc/x86_64-linux-gnu/15/cc1`:
  SHA-256 `30510b346885152c4fce41d2b501751c95d3690b1c34eaa04ebb970e70eae620`.
- `/usr/libexec/gcc/x86_64-linux-gnu/15/collect2`:
  SHA-256 `8ab5d946ba2c948e5ea5c91e25a104439302e0599a521785770d10690c565437`.

External mode, byte-count, symlink and resolved-path records are retained
with the operator receipt. Their before/after equality is required in addition
to the repository and tool/configuration comparisons.

## Checkpoint acceptance and retained-input boundary

Independent reviewer `/root/task0046_reviewer` cleared the full code and
technical checkpoint at the tested pin. Coordinator `/root` accepted that
checkpoint after independent review and its own raw receipt/input readback.
Developer and sole Cargo operator is `/root/task0046_developer`,
requested and dispatched as `gpt-6.1-sol` with `medium` reasoning effort.
All 31 case sections above retain their complete positive, negative and
compound observations. Original TASK-0045–0048 criteria close on the connected
behavior and final gate; TASK-0049's product-checkpoint criteria close on the
same receipt. Its artifact-cleanup criterion is fulfilled by the reviewed
retirement and
retained readback below. The conditional Main integration guard is
untriggered; this record claims no Main gate or integration.

The gate pins every file, including Markdown, at the exact tested commit.
Later acceptance prose is not a literal gate pass at another all-file input
fingerprint. Executed source, tests, configuration, fixtures and runtime
fingerprint must remain equal to that tested inventory; manual Markdown,
local-link and authority review covers the changed receipt prose. The
acceptance-retention readback below precedes cleanup.
No resource, stack, work or capacity limit was widened. Cell lifetime remains
exactly its resource scope, with strict payload outlives ordering, cycle and
payload-crossing rejection, and unchanged native retained-owner protections.
DN-0054 remains byte-identical and separate. No remote publication, PR, Main
integration or branch/worktree/cache retirement is part of this checkpoint.

## Local acceptance retention and transition retirement

The reviewed acceptance update was retained at unsigned local commit
`97792795d9d53285844e4ff6f5a7a2a02bbfa366`, tree
`d4429549ce3c4451b93bd288f05898b121243c95`, directly after the tested
checkpoint. Its clean 1,769-file inventory SHA-256 is
`6e802c91f0e65ad090b657692bedc73bc14061d563093d9db70e4c93755e4877`.
Only the six reviewed receipt Markdown files changed; all 1,763 other files,
including executed source, tests, configuration and fixtures, match the gate.
There is no commit signature. Independent review and coordinator readback
cover the retained acceptance, not a new code-gate invocation.

The separate reviewed lifecycle delta removes exactly ten transition files:
the accepted proposal, TASK-0045–0049 and four execution plans. It changes
exactly five surviving documents: this evidence, the task/proposal/design
indexes and DN-0053. DN-0053 remains informative and retained because the
byte-identical DN-0054 links to it. No unrelated artifact, source, test,
configuration, fixture, worktree or build cache is removed or changed.
The retained retirement readback verified actual file absence, repaired local
links, current specification authority and equality of every retained executed
input. This fulfills TASK-0049's lifecycle criterion. The conditional Main
guard remains untriggered.
Main integration has not occurred.

### Local transition history

The proposal, original complete criteria, acceptance marks, historical roles
and execution plans remain in the local acceptance object. These commits have
not been pushed; remote publication is not implied. Retrieve all ten exact
artifacts with the following verified local Git commands:

```sh
checkpoint=97792795d9d53285844e4ff6f5a7a2a02bbfa366
artifact=docs/proposals/CP-0023-scoped-generic-cells.md
git show "$checkpoint:$artifact"
artifact=docs/tasks/TASK-0045-generic-cell-api-and-acquisition.md
git show "$checkpoint:$artifact"
artifact=docs/tasks/TASK-0046-generic-cell-contents-and-dependencies.md
git show "$checkpoint:$artifact"
artifact=docs/tasks/TASK-0047-generic-cell-execution-and-completion.md
git show "$checkpoint:$artifact"
artifact=docs/tasks/TASK-0048-generic-cell-integrated-verification.md
git show "$checkpoint:$artifact"
artifact=docs/tasks/TASK-0049-close-generic-cell-checkpoint.md
git show "$checkpoint:$artifact"
artifact=docs/tasks/task-0045-execution-plan.md
git show "$checkpoint:$artifact"
artifact=docs/tasks/task-0046-execution-plan.md
git show "$checkpoint:$artifact"
artifact=docs/tasks/task-0047-execution-plan.md
git show "$checkpoint:$artifact"
artifact=docs/tasks/task-0048-execution-plan.md
git show "$checkpoint:$artifact"
```

Current language rules are in the specification; this evidence supplies no
additional semantics or permission. The checkpoint preserves Cell's exact
resource-scope lifetime, strict payload ordering, resource-cycle rejection,
ordinary payload-crossing and all native retained-owner protections. DN-0054
SHA-256 remains
`c7a596a9fbd84029adfd5333af02594e1a82eea30c548947be362f722cd1e342`.
No push, PR, Main integration or branch/worktree/cache retirement is included.

## Retained cleanup readback and local closure

The actual lifecycle delta was retained unsigned at local commit
`9807f6d45326a4fde08a422037c186596f3d781a`, tree
`91f47ce7039c322128ed42460c4e4e94d120e824`, directly after the acceptance
commit. The retained tree is clean and contains no commit signature. All ten
retired paths are absent, rather than empty files. Exactly the five reviewed
surviving Markdown documents changed. The 1,759 retained mode/content records
have SHA-256:
`cbbe9a25a13a7887d3bd33989f4c8d37b1867e25842c93a5688078c606cfceac`.

All 1,754 other retained records match the tested `7e80df3e` inventory,
including executed source, tests, configuration and fixtures. The current
runtime fingerprint remains `6270711a` as fully identified above. Manual
readback verified 125 relative file/anchor targets across the five surviving
documents and no stale retired-artifact links in surviving documentation,
specification or agent Markdown. All ten local historical retrieval commands
resolve to their exact acceptance objects. The 31 distinct primary case
sections remain. DN-0053 is retained; DN-0054 has its unchanged hash above.

Independent reviewer `/root/task0046_reviewer` and coordinator `/root` cleared
the actual retained cleanup before this final evidence-only closure update.
This fulfills the last applicable TASK-0049 lifecycle criterion and closes the
local TASK-0045–0049 checkpoint, including TASK-0046's original compound
acceptance. Main integration remains unauthorized and unperformed; its
conditional guard is untriggered. No push, PR, branch/worktree/cache retirement
or separate DN-0054 work is claimed.

The fresh complete code gate remains bound to `7e80df3e`, not a later
all-file documentation fingerprint. This final update changes only the
evidence Markdown and receives manual authority/link review plus retained
executed-input equality readback. The raw gate, native and prerequisite
records remain outside the build cache; this document retains their complete
command/result/input/tool/log digests and local historical locators.

## Local Main integration — 2026-10-20

The human authorized local Main integration. The unsigned explicit merge
`849fa6f408ebbfea9a3973bc841e1f693142a788` has parents
`67ba281d4e93dbfad65e5fd1e6a34c3dfb132686` (refreshed `origin/main`) and
`9756383d176f23ae325f36cd4d614f8c16994be2` (`codex/generic-cells`). Its tree
`bf1aad4980c5bd8cf620991198906222d4258cdd` exactly matches the checkpoint.
The fresh default seven-stage gate ran on that frozen candidate with one Cargo
job, no reused or filtered stages, the genuine SQLite 3.46.1 static archive
and all 30 explicit external inputs. All seven stages passed freshly. The 140
parent harnesses report 4,112 passes, zero failures, one optional calibration
study ignored and zero filtered tests. Nine nested harness summaries are
excluded from that total.

The retained records are outside the build cache at
`.worktrees/generic-cell-main-integration-evidence-20261020/`.
`launch.json` retains the complete command and explicit observer environment
overrides;
`before.json` and `after.json` retain the equal all-file input inventories.
The gate summary, seven stage receipts/logs and operator receipt have these
digests:

- `gate/latest.json`: `baee4686a4d58d54f8fdd00d98869834fa45499ae3d3582e4a53b3f7c242ab44`.
- `operator-receipt.json`: `765fce6576f237828647e8edcd813e04b8f4c2436ab793f611abcdeceb0e0393`.

Format stage receipt SHA-256:
`58b9b05eab5a933a40bc3bf2810625d9c90608bf5dc5d10856f9d201e65015b1`.
Log SHA-256:
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Metadata stage receipt SHA-256:
`c575e783f4b11b61df02d5f03e4c96c6876a2743fc735222de49427e9ca9e717`.
Log SHA-256:
`6b5d88f0feb5de4b5f95039b3ffcf291c493b3d92b663658264b8cb2ac8c37a7`.

Check stage receipt SHA-256:
`13c6db79ee023e124f9a94bbc7f0056448efd0eb7708e48b38c27e7fc1f0a931`.
Log SHA-256:
`a51aede1546a3145e51e3669479e1b1cf857d5205d2584b82c62441074ab8217`.

Build stage receipt SHA-256:
`4cdbd5e7c1e7ab0a9552cce2bc85b58d31e625d0bdff830f6d23d8edfebd69a1`.
Log SHA-256:
`d3fa026151c4b518e159c46bba7cf6aabab416d03f0bd6a58bf81de358febb7e`.

Clippy stage receipt SHA-256:
`895294ccc29a929b5847960c723b0586838d120a72bf6482f8387de1f085e958`.
Log SHA-256:
`81a5c30fc6cf1957f02eed17e6920af99e48fbdb76c34a0b6bffb92140bada30`.

Test stage receipt SHA-256:
`2233e032da5c57bd07c0c006673b291cb760df0b913c996a45d37569f979f81f`.
Log SHA-256:
`be5401df5ef9745b6aa1cc6c85c241644052f10af3461cc61a2442e06e3478c9`.

Documentation stage receipt SHA-256:
`e9c3bd45b2c7570b0433aacb62f1823211d89cf48076c156b56e8eb97f12d3ad`.
Log SHA-256:
`dfbfa746f13222f26c1fdc2a354b245dd12d553da64877be1d0754a873ee3bb8`.

Repository files, configuration, tools, runner, canonical environment and all
external byte/count/mode/symlink/resolved-path records match before and after
the run. The observer environment explicitly includes `ASH_OWNER_EVIDENCE_DIR`;
this is fresh evidence. The earlier checkpoint run used a different observer
environment.

The fresh C06 native pair embeds runtime fingerprint
`1726d5f5b691a5d5ec0dc8a2e435e907fa43412284ebae7ff4e7a035cdc704e2`
for the all-feature, resource-calibration-matched compiler/runtime configuration.
The permitted host returns `Completed(42, RetainedError(()))` with parent final
byte 99; the denied later borrow exits 1 before native entry with parent byte
0. Both acquire parent64/child4, retain child4 and release child4 then parent64
exactly once. `native-readback.json` SHA-256 is
`30d089c7acdb76341d3d4e14d673a3f17e32648eb29edf39f8094ee871612f42`.
It records identities for all 19 retained files per host, case-preimages,
native compile/link
commands and actual resolved-library pins. Companion `.comment`, ELF
program-header/dynamic and symbol logs retain compiler, interpreter and linkage
observations. The earlier default-feature native receipts remain historical;
missing old temporary artifacts supply no current equality proof.

The genuine archive SHA-256 remains
`7c2b4dc4aa149543e60252b5fffcb62088398470a09885cebb5e3120459c0617`.
The retained ZIP, C, header and object match the earlier five byte pins; all
selected C/Rust tools, linkers and shared-library bytes match the 30-input
inventory. Fresh symbol and ELF readback accompanies the prerequisite record.
The old temporary build receipt was unavailable and is not claimed recovered.

Independent reviewer `/root/merge_reviewer` cleared the frozen candidate and
raw gate/native evidence; coordinator `/root` accepted those results before
authorizing ref movement. The atomic ref transaction preserved the old local
Main tip `3e6326390cb182b211328682df9591d5c0311fc3` at
`archive/planning/main-before-generic-cells-20261020` and moved local `main`
to `849fa6f408ebbfea9a3973bc841e1f693142a788`. Its six unique planning
commits were not merged into product history. `main-retention.json` SHA-256 is
`883bf981bf10249f0138c138047c03d1c1b352507156ab68a10bd30ee37bd0a3`.
The clean retained tree, merge parents and absence of a commit signature were
read back. The existing product checkout switched to Main at the same tree;
the unrelated planning checkout's branch, HEAD, dirty-file bytes and status
remain equal. The checkpoint branch remains at `9756383d`, and the delivery
branch remains at `849fa6f4`. `origin/main` at the final pre-merge fetch was
`67ba281d`. No push, PR, branch/worktree/cache retirement or DN-0054 work is
included. DN-0054 remains byte-identical at SHA-256
`c7a596a9fbd84029adfd5333af02594e1a82eea30c548947be362f722cd1e342`.

This acceptance update changes only five Markdown documents. Its manual
writing, link and authority review and retained executed-input equality
readback cover the prose delta; the full gate remains bound to the merge tree.
The current specification owns the integrated language rules. This record
closes the formerly conditional Main integration obligation while preserving
the historical checkpoint boundaries and all resource-scope lifetime, strict
payload ordering, resource-cycle, payload-crossing and native-owner protections.
