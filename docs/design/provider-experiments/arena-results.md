# Scalar arena results

This is evidence for the bounded experiment governed by [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md) and [candidate A-0](semantics.md#selected-arena-contract-a-0), not current Ash semantics or accepted architecture. The selected storage fragment is Unit, Bool and checked signed-64 Int. Wider stored payloads, reference-containing graph sharing and explicit graph copying remain future work.

## Regression-only scope and deferred work, 2026-10-09

The user narrowed active work to regressions against verified integrated
`f23ea778189cc0f3ae1ec37a98219fdbcb7e4155`: Common resources/control, SQLite
String/TEXT copying and scalar Arena allocation/loading. No new feature is part
of this delivery. Fresh connected verification passes the established contract; only a
reproduced failure of that baseline justifies a code repair.

The wider experiment is preserved in unsigned recovery commit
`1aef8c15d454d26db5b0c74fcb378b9aa2b2afe9` on
`codex/arena-provider-recovery-20261009`, tree
`8dc2827adbcecbe1955d7a0daeffd65972ee7006`. All 92 owned file hashes match
that checkpoint. It includes source, fixtures, task, plan, execution record and
unfinished repairs; it may not compile and is not a verified delivery. A separate
1,834,128-byte working-file archive has SHA-256
`65392eb968c07af6d0b9d244f0204bf2f4eb41a967f2c1acf4f132074c42ca20`.
Both it and the frozen failed-round receipts remain under
`.worktree/recovery/arena-completion-20261009`. Unrelated drafts, all 33 stashes,
archive references and other worktrees are preserved.

| Deferred scope | Evidence and remaining work |
| --- | --- |
| Wider payloads, immutable graph sharing, closures, nested loading, copying and scratch scopes | Partial implementation. Round 22 passed seven wider tests but failed eleven; round 24 passed four and failed fourteen. Intermediate positives in failed rounds do not establish an accepted capability. Restore exact dispatch/context precision and complete connected native, ownership and integration gates before resuming delivery. |
| Abstract Layout forwarding and finite borrowed families | Partial implementation and source/Core checks; no complete delivery. Prepared source receipts must survive trusted cleanup row changes without granting executable authority. |
| Generic stored Ref/Link, nested terminal composition and borrowed-family discard | Never passed their required connected gates. Generic composite substitution loses information; terminal composition rejects an outgoing payload; borrowed discard fails completed capture authentication. Contextual substitution and cleanup-proof replay are unfinished. |
| Graph discard work budget | Never completed its wider gate. Repeated type-universe comparison exhausts the existing final allowance. No larger work or stack limit is authorized. |
| General borrowing, retained SQLite inputs/views and cycles | Unimplemented future DN-0036 scope. Sharing-preserving cyclic copy and broader memory policy require separate contracts. |
| Owner transport | Explicitly excluded from DN-0036; it is not an unimplemented obligation of this experiment. |

Round 24's strict lint, 45 architecture tests and seven scalar tests passed;
its exact experimental library group passed 26 and failed three, and the nested
terminal test failed. Those source pins and failures remain separate from both
the earlier partial positives and the fresh baseline receipt. No wider source is
merged. These are informative experimental findings, with no language-semantic
adoption, production-architecture acceptance or new Main merge/push.

The [regression disposition receipt](arena-regression-2026-10-09/README.md)
retains the recovery manifest, failed-round source identities and independent
review. Fresh connected verification passed 39 public cases, five existing
stack/dictionary regressions, 49 adapter unit cases and ten backing cases, plus
all five packaged SQLite hosts and scalar Arena. No baseline regression was
reproduced, so this delivery changes no executable source. The single actual
integration gate passes at unsigned merge
`7e754bd89b32acad2caa87620c7ea84af3c49e89`, tree
`a372685987f567c568978c82df2f0d5f82020600`: all six stages, 3,475 passes,
zero failures and one existing ignored calibration case across 119 outer Cargo
targets. Nine nested child summaries are excluded; four targets execute no
cases. Its tested 403 Rust/Ash/Cargo hashes, six draft hashes and HEAD remain
unchanged. The later documentation-only tracking commit retains that executable
source; it does not constitute a second gate. The linked receipt records exact
merge parents, log hash and supplemental native-source equality. Main remains
`f23ea77`, and the wider recovery branch is excluded from integration ancestry.

## Verification boundary

The unsigned scalar source delivery is `ffa1d8ef4178cb1e5651411162ff09c117b725f7`. Its 352-file source manifest is `round-retention-lint-pins.json`, SHA-256 `3d351316ad975160a55343e3f0f6cc37de4c23655e2bbd6e431219d360feabc3`. The [selected receipts](arena-selected-2026-10-08/README.md) retain exact source identity, commands, results and native observations.

The earlier functional closure used `round-compile-repair-pins.json`, SHA-256 `833bcb70c551b5e746579d08ffee53931c6ac4f5a20f862e02e4a29718ccf976`, preserved by recovery commit `1824bb70b28c72da2dbc6308887c4577b5adb681`. It passed 1,674 library tests and all seven public arena tests with no failures or ignored cases. Execution took 127.54 and 4.34 seconds respectively; those durations establish no performance improvement.

The final source adds reviewed mechanical and inventory corrections. Its collected check round passes both affected architecture tests, strict workspace/all-target/all-feature lint, 41 adapter unit plus ten backing tests, native41 and formatting. Each command ran against unchanged source pins. These checks remain distinct from the completed Original gate. The complete Original gate passes at `7a518e83230fec568978b269b1d69776ab6051c5` and tree `8af28e134fbe17e19034d77bf56335a9a6bc6421`. All six ordered stages complete: format, metadata, build, strict lint, workspace/all-target/all-feature tests and warning-denied documentation. Outer Cargo target summaries record 3,475 passes, 0 failures and 1 ignored case (the generated calibration fixture) across 119 targets; 4 targets contain no executed cases. Nine nested child summaries are excluded from these totals. The [combined-delivery-2026-10-08 receipt](combined-delivery-2026-10-08/README.md) retains raw output, exact commands, the corrected outer-target summary and unchanged source/eight-draft evidence.

Main merge `f51f538455cb997e5e1f5db6eec8cf36d616c7d1` retains Common `f56070ccb88d21ba833c5ca70106070318b9145a`. Focused verification at this Main source passes 39 cases across six Cargo targets, with 0 failures and 0 ignored cases. All five packaged SQLite hosts and the selected scalar Arena host pass their recorded source/native assertions. The [main-delivery-2026-10-08 receipt](main-delivery-2026-10-08/README.md) retains exact commands, raw logs, source pins, phase measurements and cleanup disposition. The full workspace gate belongs to Original `7a518e83230fec568978b269b1d69776ab6051c5`; its documentation descendant `f56070ccb88d21ba833c5ca70106070318b9145a` and this Main merge retain the executable source. Later result prose does not constitute another full gate. Broader TASK-0034 payload/graph-sharing/copying work and paused Lean/Core/proof work remain unfinished and excluded. This retains informative DN-0036 evidence without semantic or production adoption or a formal proof.

The inventory scanner now distinguishes module/type/value namespaces, preserves metadata from module-only facades, and follows genuine aliases without weakening cycle or missing-type refusal. Six entries follow their relocated physical declarations; the method-occurrence cache records its owned type and shared evidence paths. Earlier failed logs and aborted compilation remain historical evidence outside this selected receipt set.

## Actual storage and control

[allocation-entry.ash](../../../tests/fixtures/provider-experiments/arena-typed/allocation-entry.ash) acquires capacity `(8, 1)`, stores 41, reads the actual eight bytes, and returns `Completed(41, Closed)`. The final `round-retention-lint-native41.log` records Acquired → Stored → Loaded → Released for the same activation/object, eight used payload bytes, one object and `host_teardown: false`. The public test separately requires zero retained owners.

The executable host example registers both canonical manifests and attaches `arena_binding` using the original memory-manifest Arc also retained by module roots:

```bash
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo run --locked -p ash-foreign-adapter --example arena_typed -- tests/fixtures/provider-experiments/arena-typed/allocation-entry.ash
```

The seven passing public cases in [provider_arena_allocation.rs](../../../tests/provider_arena_allocation.rs) establish:

| Case | Recorded behavior |
| --- | --- |
| Mixed Int/Bool | Actual Store/Load; distinct objects under one owner; 9 bytes and 2 objects. |
| Capacity, range and alignment refusal | Earlier bytes, reference, cursor and object count survive; the earlier object still loads. |
| Signed-64 maximum | Loads 9223372036854775807. Minimum/lower-overflow remain native codec evidence because these source fixtures lack negative literal syntax. |
| Two Unit objects | Zero payload capacity; distinct object records and two actual loads. Alignment padding still consumes payload capacity. |
| Ordinary source handlers | Refusal emits no Store; a load override returns 99 without a native Load; an allocation override reuses an earlier genuine Ref without another Store. |
| Imported implementation | Concrete `Input<Int>` with explicit StorageProvider/Layout prerequisites executes real Store/Load and returns Allocated(41). |
| Local aggregate/closure | Uses a live Ref and returns independent 82; paired extracted-Ref escape cases reject. |
| Sealed evidence and access refusal | Source impl/lexical Layout reject as SealedProvider; direct Ref escape as ResourceEscape; wrong-owner/fabricated tuples as Argument. Native41 is a prerequisite and refusals produce no native events or retained owners. |
| Outward clause request | ResourceEscape with exact primary/related resource spans; a body-demanded Bool member does not discharge the clause's outward request. |
| Grouped resume | `Completed((82, true), Closed)` with four actual loads under the original activation. |
| Owned discard | `(42, 41)` after Int then Bool cleanup loads, followed by exactly one normal release. Exact events exclude abandoned-body reads, reacquisition and host teardown. |

Local use of an aggregate containing a Ref is not evidence for storing Ref-containing payloads.

## Authority and regression evidence

Prepared and Admitted groups retain distinct borrowed source views. Each authenticates the exact current dictionary bindings and native-flow projections. Ordinary concrete Layout occurrences separately retain the original sealed catalogue/anchor, selected producer and actual intrinsic header. Current origins do not replace original authority. These source facts grant no independent final Layout token.

Direct generic `Layout.witness` invocation now differs from dictionary installation. Its original requirement, family formal, method, complete pure Unit-to-canonical-Witness header and actual source occurrence are authenticated before invocation produces independent metadata. A completed source projection supplies an immutable loan of its exact node and route slices; a copied descriptor alone grants no authority. Capture accepts only its exact indexed original route and header. Only the authenticated rigid payload's metadata slots receive the corresponding source-analysis fact.

The existing nested fixture exercises direct calls, value aliases, captured Witness values, captured dictionary callables, and ordinary Int-result helpers. The returned helper witness supplies the actual native Store layout, and the Int-result helper supplies alignment zero. Original source checking and independent Core validation, both identity/fold transformations, and rejection of a different genuine same-typed/same-producer dominating dictionary binder all pass. General opaque data, raw installer values, owner/state/reference permissions and final admission remain restricted.

The genuine source-loan observer passes exact, one-short and fresh retry checks at prefixes 0 and 17, plus cloned-slice, copied-route and wrong route/binder/header refusals. Source receipt, admitted view, original concrete occurrence and both-cache cleanup rollback regressions pass in the full library. The two unchanged 64 KiB stack regressions also pass after complete control-discovery and compiler-frame repairs, without increased stack/work limits or weakened retry assertions.

The final adapter receipt records 41 unit and ten backing passes on the delivered source after its verbatim source-item reorder. Actual typed Store/Load reply rejection preserves published bytes/usage, abandons pending publication or observation, quarantines the owner until runtime drop, then performs one host-teardown release with zero outstanding backing. Terminal host failure does not run source cleanup as recovery. The complete Original gate is recorded above; source identity and receipt boundaries remain separate.

## Costs and assumptions

The final native41 host receipt completes all three compilation phases:

| Phase | Used work |
| --- | ---: |
| Source checking | 88,793 |
| Final elaboration | 27,096 |
| Independent Core | 82,277 |

These are observed work counts for the named frozen source. They are not a memory measurement, universal tariff, or proof that every admitted program finishes. These Arena repairs did not raise the previously calibrated phase budgets or existing depth and stack limits. The separate [calibrated-admission policy](calibrated-admission-2026-10-08/README.md) records the larger user-authorized public-driver allowances and their finite margins. Exact/short/prefixed internal authority tests exercise their own production consumers; they do not measure complete compilation phases. Payload-byte and object counters exclude compiler metadata, native table allocation, codec scratch and the evaluator heap.

Safety relies on the native adapter's arithmetic, alignment, bounds, initialization, scalar encoding and exact owner/object/layout checks. Conversion and reference/result admission precede Store publication; failed preparation preserves previous objects. Load authenticates a live owner and decodes actual bounded bytes. Original manifest identity and independently checked Core connect those foreign assumptions to source execution. Evidence consists of finite testing and reviewed arguments, without a mechanized preservation theorem.

Packed/nominal layouts, stored references, graph sharing, deep or recipient-arena copying, borrowing, owner transport and wider memory policy need later evidence. SQLite transfers registration/provider/admission/completion experience, not Arena object-layout safety. Production adoption still requires the proposal/decision and specification workflow.

The [inner-owner source-refusal sketch](../../../tests/fixtures/provider-experiments/arena-typed/inner-owner-source-refusal.ash) records an open placement question. Its exact outer-owner handler refuses allocation and retains no inner reference in outer storage; an unselected native fallback still cannot be specialized outside the fresh inner payload owner's scope. The sketch remains unexecuted in this scalar delivery, and no useful-case admission or placement alternative is claimed.
