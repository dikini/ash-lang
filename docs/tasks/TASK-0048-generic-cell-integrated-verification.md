# TASK-0048: Generic Cell Integrated Verification

- ID: `TASK-0048`
- Status: active
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

- [ ] CELL-C03: original, imported, copied, restored and transformed Core agree;
  every specified tamper fails independent admission.
- [ ] CELL-C04: all named layers pass exact/insufficient/retry budget probes
  with no partial permission, publication or mutation.
- [ ] CELL-C05: live/captured capacity, shared payload and deep-disposal checks
  preserve accounting and iterative execution without relaxed limits.
- [ ] CELL-C06: legacy and ash-ffi regressions plus the mixed quarantine case
  establish retained native protection and denial before native entry.
- [ ] All 31 case receipts are connected to the same candidate or have explicit
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

None recorded. Record measured bounds and failures with their exact inputs.

## Deviations

None authorized. No general region mechanism, native lifetime relaxation,
alternative legacy API or verification-policy change belongs to this task.

The [31-case observation map](../design/generic-cell/evidence.md) records the
working source/Core/runtime/native boundaries and exact-work probes. Frozen
verification and the independent retained review remain pending; TASK-0049's
fresh complete gate is still required before original compound acceptance.
