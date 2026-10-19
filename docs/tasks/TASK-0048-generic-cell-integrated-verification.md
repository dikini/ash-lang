# TASK-0048: Generic Cell Integrated Verification

- ID: `TASK-0048`
- Status: completed
- Related: [CP-0023](../proposals/CP-0023-scoped-generic-cells.md),
  [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md),
  [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md),
  [TASK-0047](TASK-0047-generic-cell-execution-and-completion.md),
  [TASK-0049](TASK-0049-close-generic-cell-checkpoint.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

Execute connected verification on the combined TASK-0045–0047 implementation
and its frozen product commit. Test preparation can begin earlier; it cannot
establish acceptance before those implementations connect. Layer owners must
already implement charging and independent validation; this task does not defer
those obligations or grant permission for partially checked public support.

TASK-0049 records the retaining branch, build operator and checkpoint gates.
Use the selected ash-ffi descendant and compatible generated native host rather
than the older planning checkout or an unpinned prebuilt binary.

## Work

1. Add adversarial Core and summary cases for complete `R,T`, owned position,
   origins, provider/operation facts, rows, possible target owners, hidden
   captures and contents flow. Test direct, imported, copied, restored and
   transformed inputs, including private program-image capture/restoration and
   its builtin module-role authentication. Verify independent rejection rather
   than trusting source permission or forged body-free summaries.
2. Exercise exact sufficient, one-short and fresh retry budgets for inference,
   recursive summaries, Core construction/validation, acquisition and write
   preparation. Observe publication/mutation boundaries and already performed
   operand effects. Record the ledger and refusal phase for each probe.
3. Measure live and captured capacity, large shared payloads and deep normal,
   discarded and failure disposal. Check charging before proportional work and
   retention, iterative teardown and unchanged work/depth/stack policies.
4. Run the complete legacy integer-cell regressions and relevant ash-ffi
   payload-crossing, State/data, native retention, blocked teardown and host
   destruction cases. Add the mixed C06 scenario: C stores enclosing native A's
   access, B retains and quarantines A inside C, reading the stored handle is
   permitted, and native use through it remains denied before native entry.
   Closing C must neither consume A nor remove native dependency protection.
5. Collect actual public-path results from all case owners, including P12/P13/N12
   and recursive activation counts. Repair implementation defects within the
   accepted contract with the owning developer; return semantic gaps to CP-0023.
   Keep real native observations separate from injected failure evidence.

Start from baseline `tests/resource_scope_core.rs`,
`tests/resource_scope_modules.rs`, `tests/resource_scope_runtime.rs`,
`tests/core_validation.rs`, `tests/source_resource_execution.rs`,
`tests/source_resource_acquired_only.rs`, `tests/program_build.rs`,
`tests/program_build_native.rs` and the owning tests in `src/eval/`, `src/core/`
and `src/build/image.rs`. Extend the existing ledgers and test seams instead of
adding an alternative permission or uncharged test path.

## Progress

Integrated verification is authorized from retained unsigned
`9cfd39a9a9f82e265cd82bbc73d438dc4968d357`, after TASK-0047 runtime component
readiness and independent retained readback. The task-owned
[execution plan](task-0048-execution-plan.md) records the sequence. All original
criteria remain open until their complete matching observations and checkpoint
gate exist.

- [x] CELL-C03: original, imported, copied, restored and transformed Core agree;
  every specified tamper fails independent admission.
- [x] CELL-C04: all named layers pass exact/insufficient/retry budget probes
  with no partial permission, publication or mutation.
- [x] CELL-C05: live/captured capacity, shared payload and deep-disposal checks
  preserve accounting and iterative execution without relaxed limits.
- [x] CELL-C06: legacy and ash-ffi regressions plus the mixed quarantine case
  establish retained native protection and denial before native entry.
- [x] All 31 case receipts are connected to the same candidate or have explicit
  input-equality justification; gaps are returned to their primary task owners.

## Verification

Use focused owning unit tests and the relevant source/Core/runtime suites from
TASK-0045–0047. Run the connected adversarial and native suites, for example:

```sh
CARGO_BUILD_JOBS=1 cargo test \
    --test core_validation --test resource_scope_core \
    --test source_resource_execution --test source_resource_acquired_only \
    --test program_build --test program_build_native
```

The assigned build operator records generated-host inputs, platform assumptions,
toolchain, exact commands, ledger limits, results and refusal phases. A filtered
command is not evidence for unselected variants. A later successful run does not
replace observation of the insufficient-budget boundary. Confirm native call
and release counts in real host runs, not solely injected evaluator failures.

Deliver focused receipts and independent review to TASK-0049. The fresh complete
`cargo xtask verify` checkpoint is owned there; until it passes, full regression
acceptance remains pending even if these focused checks pass.

## Discoveries

The 64 KiB deep function test needed a test-only helper extraction after the
added discard branch inflated its shared caller frame: the observed overflow
was mode-zero acquisition before discard, not recursive teardown. Fresh actual
owned capture/discard then passed at unchanged limits with one deep root and
exact accounting/release events. The native artifact collector initially used
the generated src directory for Cargo files; its path-only repair and failed
pre-execution receipt remain separate from the successful real native pair.

## Deviations

None authorized. No general region mechanism, native lifetime relaxation,
alternative legacy API or verification-policy change belongs to this task.

### Focused readiness receipt

The [31-case observation map](../design/generic-cell/evidence.md) retains exact
commands, phases, values/counts, refusal reasons, tool/input/native bindings and
all nine raw-log digests. Independent code/technical review is clear and root
accepted bounded TASK-0048 focused readiness on 2026-10-19 at unsigned
`b785e5605569492103a64ffb9e2a3b5de64ded88`, tree
`70577492c6ed4297a40a2451f7e18639d0386ac4`.

Library 1,937, resource/cleanup 173, full architecture 47, declared-view one and
shared Core rank-1 one passed; the real native paired test passed with two
hosts, and strict Clippy/fmt/rustdoc passed. Five unaffected observations at
`b3445f51b6aafb6b3e7a866a438763104dd595f8` transfer across only the native
collector test-path repair, with 1,768 other mode/content records exact.
Fresh fmt/Clippy/native/rustdoc bind the repaired records; failed native
collection supplies no execution result. The retaining 1,769-record digest is
`0136ae86db4d585bec0023defebe3d893eb3b7048b20b50aca92c5bc99201b85`.

Both actual hosts embed
`b8c62ad3ad13fab49c6cd4197f7d14d395eb0628f187e0bd8829bc57d58e1fce`.
Permitted stored-handle reads and C close preserve retained native protection;
subsequent Owner.borrow provider/State access is denied before native entry.
The real traces distinguish completed result 42/parent byte 99 from internal
refusal/byte zero, with child-before-parent release once each. Native readback
SHA-256 is
`a525773b3239dce15847f996211244737dd5092b9adf05ba3e766293d7d499f9`.

Fresh actors remain developer/Cargo operator `/root/task0046_developer`,
independent reviewer `/root/task0046_reviewer` and acceptance owner `/root`;
the dispatched model/effort remains `gpt-6.1-sol`, `medium`. One Cargo job,
Rust 1.97.1, empty RUSTC_WRAPPER and the existing cache were preserved. Working
receipts live outside the cache under `/tmp/task0048-launch/frozen/`.
Reviewed receipt prose and explicit existing-scope specification wording change
after the tested pin; retained readback preserves all executed source, tests,
configuration and fixture bytes. Original criteria stay
unchecked. TASK-0049 owns the fresh default seven-stage workspace gate and
original compound acceptance, followed by authorized lifecycle cleanup.
No push/Main integration, DN-0054 change or retirement is included.

## Local checkpoint acceptance, 2026-10-19

The complete connected checkpoint was verified at
`7e80df3e66a6d3074b86f29b7582cadb6696a563`, tree
`dd26e7d5a2218cdf374c626af7759e558b8105ef`. The fresh default complete
gate executed all seven stages without reuse or filters: 4,112 parent-harness
passes, zero failures and one optional native calibration study ignored.
Nine nested child-process summaries are excluded. The
[complete case map and receipt](../design/generic-cell/evidence.md)
retain all 31 primary cases, their variants, owning ledgers, native inputs,
commands, results and digests. This closes connected product criteria rather
than relying on earlier component readiness.

Independent checkpoint review and coordinator acceptance are recorded in that
receipt. TASK-0049 lifecycle cleanup remains pending until the separate
reviewed deletion/index/link delta is retained and read back. Main integration
has not been authorized or performed; its conditional verification guard is
untriggered. No push, PR or worktree/cache retirement is included. DN-0054
remains separate and byte-identical. Historical role and component receipts
above retain their original scope.
