# TASK-0047: Generic Cell Execution and Completion

- ID: `TASK-0047`
- Status: active
- Related: [CP-0023](../proposals/CP-0023-scoped-generic-cells.md),
  [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md),
  [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md),
  [TASK-0048](TASK-0048-generic-cell-integrated-verification.md),
  [TASK-0049](TASK-0049-close-generic-cell-checkpoint.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

Use TASK-0045's reviewed authenticated carrier foundation and CP-0023's
execution contract on the ash-ffi base named in TASK-0049. Runtime work may
proceed alongside TASK-0046, with shared-file coordination. Public execution
requires TASK-0046's completed source/Core dependency admission; runtime keys
cannot replace that proof. No task's positive acceptance is complete until the
connected public path supplies its required observations.

## Work

1. Generalize the owned runtime payload root to an ordinary checked value while
   keeping the new and legacy APIs distinct. Preserve fresh activation keys,
   lexical type/row instantiation, non-owning handles and exact operation/type
   authentication. Reads share values; they do not deep-copy or freeze cells
   reachable through a snapshot.
2. Evaluate initialization once and operands in source order. Admit work,
   storage and capacity before publication or replacement; a refusal cannot
   publish a partial cell or partially mutate its root. Existing operand effects
   remain performed. Charge every new proportional path in its owning ledger.
3. Preserve source handler precedence, clauses bypassing their selected handler,
   restored handlers at resume, direct and indirect mutation, and the actual
   handler reply. Implement the stateful scenarios without a special pure-
   override assumption. Primitive slot transitions invoke no user callback.
4. Capture/resume must move the same owner and latest payload without reacquiring
   or copying ownership. Normal return and checked discard remove the root
   once after required inner completion. Cleanup can use still-live enclosing
   cells; outside or running completion cannot be skipped.
5. Count captured scopes toward live capacity, preserve fresh keys on reuse and
   dispose deep roots/control iteratively. Keep internal failure distinct from
   source cleanup or recoverable allocation. Do not consume referenced native
   owners or restore access revoked by quarantine.
6. Supply runtime evidence for every positive case owned by TASK-0045/0046,
   especially helper/facade aliasing, recursive activations, immutable cycles
   and the stateful snapshot pair. Update dynamic semantics and affected
   execution documentation with the implementation.

Start from baseline `src/eval/machine.rs`, `src/eval/value.rs`,
`src/eval/instantiation.rs`, `src/eval/disposal.rs` and `src/eval/failure.rs`.
Keep the explicit evaluator-machine and typed Core boundaries; shared legacy
implementation is optional and must preserve its behavior.

## Progress

Implementation is authorized from retained dependency handoff
`ee306d161478d2b135c503d7b79056f8b0dfa32b` on `codex/generic-cells`. The
task-owned [execution plan](task-0047-execution-plan.md) records the sequence.
All original acceptance remains pending until its complete observations and
checkpoint evidence exist.

- [ ] CELL-P07: exact read override, no-other-mutation intercepted write,
  forwarded write and dropped self-capturing replacement have their specified
  results; the discarded replacement creates no retained slot edge.
- [ ] CELL-P12: the unforwarded original write plus the Tick handler's separate
  mutation leaves `99`, not `41` or the original replacement `42`.
- [ ] CELL-C01: capture/resume observes the latest payload without reacquisition;
  nested/same-site activations stay distinct; donor/stale keys fail before access.
- [ ] CELL-C02: owned discard closes once after dependent cleanup; unsafe outside
  or running abandonment rejects; initializer capture creates no premature owner.
- [ ] Runtime observations for all TASK-0045/0046 positive cases are delivered
  to their primary owners, including P05 release counts and P13's result.
- [ ] Runtime charging, preparation, iterative disposal and failure probes are
  connected for TASK-0048's C04/C05/C06 checks.

The primary cases include all CP-0023 variants, not only the summary above.

### Runtime connection, 2026-10-19

The shared machine now executes ordinary fixed-type generic cell roots after
source and independent Core dependency admission. The legacy integer branch
retains its existing initializer and operation rules. Generic boundaries retain
complete lexical R/T authority, authenticate the request and handle, and
prepare paid copying, alias resolution and trace storage before
publication/replacement. Capture moves the same latest root and owner; release
follows inner completion. No new region, private lifecycle profile or native
authority is introduced.

Public `run_path` observations and independent checked-machine traces cover:

| Case | Actual observation |
| --- | --- |
| P01 | `true`, `(42, true)`, nominal/alias `42`; initializer counter `1`. |
| P02 | Earlier/later `(41, 42)`; escaped earlier snapshot `41`. |
| P03 | Returned outer access reads `7`. |
| P04 | Imported earlier function escapes and calls `7`. |
| P05 | Direct/imported `9`; two distinct keys, one release each. |
| P06 | Local/import/facade and both aliases: `42`, one slot/write. |
| P07 | `99` / `41` / `42` / `7`; forward writes once, drop writes zero. |
| P08 | Dependent reply `42` locally; independent reply `7` escapes. |
| P09 | Independent `42`; enclosing-owner dependency crosses and returns `7`. |
| P10 | Cyclic prefix `2`; owning reads retain identical Location. |
| P11 | Repeated monomorphic reads with legacy nesting: `42`. |
| P12 | Separate Tick mutation leaves `99`, one actual write. |
| P13 | Escaped reply `7`; reply/later stored pair `(7, 42)`, one write. |

P07 covers exact read override, unforwarded write, forwarded write and the
self-capturing replacement discarded by its interceptor, in that order. P09's
dependent payload crosses an unrelated inner scope while its owner stays live.
P10 separately tests a finite cyclic prefix and repeated large/cyclic owning
reads without copying heap payload.

The runtime helper asserts unique acquisition keys and exactly one release per
acquisition for each P01–P13 fixture using `generic_runtime_observation`. An
indexed effectful function payload read through an imported helper calls saved
outer access and returns `7`. A rank-1 `scope<T>` helper instantiated at
Int/Bool returns `(41, true)`. Passing an argument that reads the legacy cell
through the mixed constrained-helper form returns `7`.

C01 observes both resumed values `(41, 42)`, one acquisition, two writes and
one release. C02 dependent cleanup writes `7` before inner release; initializer
discard preserves side `1` while neither inner body nor suffix runs and only
the enclosing owner acquires/releases. Separate source negatives for outside
completion and running cleanup fail in the typing phase with
`effect.discard-unsafe` and causal discard labels. The running-cleanup Core
control changes a real copied/folded
Resume to Discard and asserts the independent capture proof's Unsafe/Cleanup
result; the altered raw arena is neither admitted nor executed.

Owning preflights cover all insufficient acquisition/write prefixes and two
fresh retries with exact measured work, full payload-type mismatch, two live
same-type donor
handles, stale/fresh keys, family mismatch and a genuine foreign-arena Request.
Scope is the existing per-evaluation opaque activation namespace; no external
Value transport API or global nonce is added. Earlier strict operand effects
persist on final Access refusal: side `12`, target `41`, two earlier writes and
no target Request/result. Complete execution returns
`(42, 12)`. Preparation refusal is distinct from post-commit old-root internal
disposal failure, which reports Teardown/EnvironmentDisposal/AllocatorRefused
and incomplete cleanup before another Ash step.

Captured owners still count toward capacity; resume/discard and fresh reuse
retain latest values and fresh keys. New generic payload disposal probes cover
admitted origin bound `130` and 32,000-entry callable environments on 64 KiB
through normal release, replacement and internal failure. The unchanged
captured-control, deep completion/discard and callback regressions also pass at
their original bounds. A deep generic payload closed by actual owned discard
remains TASK-0048's C05 observation; common-path discard regressions do not
supply it. No work/stack/capacity limit changed. Stored native access remains
nonowning; real mixed quarantine remains TASK-0048's C06 observation.

Generated execution prints `7` twice after original source deletion; private
images execute `42` and imported snapshot/recursive/handler cases `7` / `9` /
`7` while retaining exact/one-short/fresh restoration controls. The documented
Bool program prints exactly `true : Bool` plus newline.

The runtime observation pin is unsigned
`8d5b3c125d042901518c9fcc413ad2c48c730382`, tree
`cf9cf9eff4f0820160df9cff4a578bbf3225056e`, directly following TASK-0046 handoff
`ee306d161478d2b135c503d7b79056f8b0dfa32b`. Its 1762 file records are in
`/tmp/task0047-launch/manifest-frozen-code.json`, with canonical SHA-256
`c8d91bf1192179e6c3d8bd4dc5a8b46517d8b604533619a9ebc03710d23dce86`.

The final inventory-test pin is unsigned
`ac72d18623724f399f1f1dfcf3a0046d63669b81`, tree
`7cab3d454aeac34f4e77c3603b382814fa6cef46`. Only `tests/architecture.rs` changes
from the runtime pin: seven physical type-owner rows and three generated-site
key corrections, within existing profiles. The scanner remains unchanged.
`inventory/manifest-code.json` has the same 1762 paths, with canonical SHA-256
`11f96a5286ad8290df680b81a89cb5189d58a9f5f2ca74be78b2a78b7b61deed`.
Its file SHA-256 is
`dbc440f82e743e279bdbdc5eb3128d75735ace1359bae73f78ce7338ddd24d00`.
All other 1761 mode/content records equal the runtime pin exactly.

`inventory/input-transfer.json` records transfer of library, resource/cleanup,
affected/native/build, Rustdoc and example observations: their production,
configuration and exercised test inputs are unchanged. The architecture target,
strict Clippy and formatting are freshly verified at `ac72d18`. The initial
candidate's Clippy/formatting receipts also retain their exact precommit-input
transfer from Git head `ee306d1`; final readiness uses the refreshed checks.
These are focused checks; TASK-0049 still requires a fresh full gate.

All commands ran sequentially in `.worktree/generic-cells`, with Rust 1.97.1,
`CARGO_BUILD_JOBS=1 RUSTC_WRAPPER=` and the existing target cache. Evidence
stays
under `/tmp/task0047-launch`. `tools-config.json` records versions, four actual
tool executable hashes and five Cargo/toolchain configuration hashes. Rustdoc
additionally used `RUSTDOCFLAGS='-D warnings'`.

```sh
cargo test --lib --locked
cargo test --test resource_scope_typing --test resource_scope_modules \
    --test resource_scope_core --test resource_scope_runtime \
    --test cleanup_abandonment --test cleanup_interactions \
    --test cleanup_partial_acquisition --locked
cargo test --test source_resource_execution \
    --test source_resource_acquired_only --test native_buffer_source \
    --test native_buffer_runtime --test native_buffer_interactions \
    --test provider_retention_source --test program_build --locked \
    -- --test-threads=1
cargo doc -p ash --no-deps --all-features --locked
cargo test --test spec_examples --locked \
    generic_cell_documentation_example_has_exact_cli_output -- --exact
cargo fmt --check
cargo clippy -p ash --all-targets --all-features --locked -- -D warnings
cargo test --test architecture --locked
```

Five transferred receipts name runtime pin `8d5b3c1`, exit zero with stable
inputs and the `c8d91b...` record SHA. Three fresh receipts in `inventory/` name
`ac72d18`, exit zero with stable inputs and the `11f96a...` record SHA. Each
records exact argv, head, environment, elapsed time, input and actual log hash.

Whole library: 1931 passed. Resource/cleanup: 170 passed (typing 102, modules
16, Core 2, runtime 32, abandonment 11, interactions 6, partial acquisition 1).
Affected/native/build: 121 passed (execution 78, acquired-only 5, native source
13, runtime 9, interactions 8, retention source 3, program build 5). Exact CLI
example: 1 passed. Architecture: 47 passed. Nested child summaries are not
counted twice. Strict Clippy, formatting and warnings-denied Rustdoc pass.
Generated-host execution uses the matching compiler/runtime fingerprint after
original source removal; the inventory-only repair changes none of its inputs.

Final log SHA-256 values, relative to the evidence directory:

- `lib-frozen.log`:
  `e8ffee18f3c46ed6118c944cd10a6d0b32e345f3ba683e1f1a3324839494ec92`
- `resource-frozen.log`:
  `839fff88f66746fae4f8615fd4e6d401939c3d82ac0d68227da78d89461ebda1`
- `callers-frozen.log`:
  `f77bf0343db4a3ed1c9439da3dfc8c525535f26761946ee604981b0ab79958c9`
- `rustdoc-frozen.log`:
  `39f63374ba067f9d3d2c56948195c10e597112c955038ca3b0d05cba935e1e8d`
- `example-frozen.log`:
  `74060f081bde72fa5a094620c3490e2bcda02381270f4c68e9d6a039731b9285`
- `inventory/fmt-frozen.log`:
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `inventory/clippy-frozen.log`:
  `ccd3c8b4ad1f5a7c7050d4cd6cc66eca863ac6bb1f127cbefd609d719142d72e`
- `inventory/architecture-frozen.log`:
  `1705f017b0b10f8a55f8e4616444d61cb68b4baa36bff778dc8da32abf00775f`

`/root/task0046_reviewer` cleared independent code and technical-evidence review
at `ac72d18`, including actual log/input/tool readback and the limited transfer.
`/root` accepted TASK-0047 runtime connection readiness, subject to the final
metadata-only retained readback. This receipt delivers runtime observations to
TASK-0045/0046; it does not complete their original compound criteria or all 31
checkpoint cases. TASK-0048 still owns the complete
transformed/restored/tamper/native
matrix, including actual deep generic owned discard (C05) and real mixed C06.
TASK-0049 still owns the fresh full `cargo xtask verify`, original acceptance
and retained cleanup/index updates. No Cargo process remains live. Worktree,
cache and useful evidence remain retained; no push or Main integration is
included.

## Verification

Extend `tests/resource_scope_runtime.rs`, `tests/resource_scope_core.rs` and
the relevant cleanup suites; add owning machine tests for malformed keys,
publication/mutation preflight, shared payloads and iterative disposal. Run:

```sh
CARGO_BUILD_JOBS=1 cargo test \
    --test resource_scope_runtime --test resource_scope_core \
    --test cleanup_abandonment --test cleanup_interactions \
    --test cleanup_partial_acquisition
```

Use the public source pipeline for admitted observations and explicit malformed
Core/machine probes only for internal-failure boundaries. Record exact values,
activation/release counts, source failures and internal failures separately.
Run connected positives through copied/transformed Core with TASK-0048.
Retain inputs, focused results, independent review and retained-commit equality.
TASK-0049 owns the full checkpoint gate.

## Discoveries

Interception suppresses only the original builtin replacement; surrounding
computations still change values and dependencies. Runtime observations retain
that distinction.

The mixed rank-1 `scope<T>` and legacy constrained-helper case exposed a
registry source-order false rejection. Header parameters are allocated before
body resource identities, so valid lexical identity positions need not follow
header source offsets. The correction classifies only a builtin identity with
its exact acquisition carrier on an actual resource node. Paid traversal and
all canonical identity, source, kind and later full authority checks remain.
Missing/mismatched carriers and reversed header order still reject.

## Deviations

None authorized. No native owner is acquired for a generic cell. Region-backed
storage, owner transport, manual release, atomic updates and DN-0054 allocation
work are excluded.
