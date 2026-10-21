# TASK-0052: Source Resource Default Startup Budget

- ID: `TASK-0052`
- Status: active
- Related: [issue #91](https://github.com/dikini/ash-lang/issues/91),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [TASK-0050](TASK-0050-checked-ffi-regions-control-program.md),
  [TASK-0051](TASK-0051-checked-ffi-contract-carriers.md)

> This task organizes an authorized compatibility repair. It does not change
> Ash semantics, resource allowances or checked execution permission.

## Dependencies

Start from retained `a301a654bff2b7caed4befc32ce038abcf85dd7e` in the existing
checked-FFI worktree. The orchestrator assigned this separate repair after PR #89
partial acceptance and before nominal/resource closure. Use unsigned author
commits, an early individual draft PR, independent exact-head review and GitHub
squash integration. Keep one Cargo job and the existing shared cache; Main and
other worktrees remain unchanged.

AD-0013 keeps standalone/private-image defaults separate from generated-host
input-derived startup gas. The failing Rust reconstruction test uses the existing
327680-unit default. It does not establish that a generated host exhausts its
separately derived allowance. Neither allowance changes here.

## Work

1. Publish this task before long implementation. Reconstruct the original source
   header/forest, copied owner and final Core authority boundaries from current
   specification and implementation.
2. Measure the existing reproducer under the unchanged cumulative default.
   Record entered and completed phases, including failure: source/module restore,
   extended registry, selected views/header, acquire/finish/handler reconstruction
   and admission, main arena reconstruction and final independent Core.
3. Count source-coordinate parsing and registry-session fresh/hit/bypass paths.
   Existing `SourceResourceStructureSession` already reuses eligible complete
   registry proofs; do not introduce redundant reuse or treat context-dependent
   bypasses as mistakes. Keep instrumentation test-only or remove it after the
   retained measurement.
4. Select a repair only after costs distinguish its cause. If repeated immutable
   declaration data dominates, reuse only that context-independent component in
   the existing bounded reconstruction/session loan. Preserve original immutable
   owners, exact source/module/registry/context association and paid hits. If that
   hypothesis fails, follow the measured phase instead.
5. Preserve independent original header/forest and final copied-scope/Core
   checks, exact native contracts/registrations, owner phases, lineage, rows,
   cleanup and capture obligations. Expected-fact byte equality supplies data,
   not Core permission. Publish no completed reuse entry on resource refusal.
6. Verify the original test cumulatively under its unchanged default, related
   import/owner/image controls, exact/one-short/nonzero-prefix/retry boundaries
   and forged/mismatched contexts. Update documentation only for implemented
   behavior. Retain commands, source/configuration pins and honest outcomes.

No budget increase, refill, reset, source-name dispatch, generic registry cache,
new executor, native execution or nominal/resource feature belongs to this task.
F-core remains a separate required checkpoint.

## Progress

- [x] Retain phase/counter measurements under the existing default.
- [x] Repair only the demonstrated cost without weakening admission.
- [ ] Original reproducer and affected boundaries pass focused verification.
- [ ] Independent review, GitHub retention and acceptance readback complete.

The [PR #89 baseline comparison](evidence/checked-ffi-selected/README.md#final-focused-verification)
reproduces the same `Resource` failure at exact retained `0a856957` and its
candidate: decode 38705, expected-fact admission 52747, reconstruction refusal at
327680. Baseline archive paths differ explicitly. Those historical receipts did not
measure the failing subphase or complete demand; the measurements below do.

## Verification

The first command is the exact existing test:

```sh
cargo test -p ash --locked --lib build::image::source_resource_image::tests::imported_buffer_two_owner_discard_has_normal_startup_budget -- --exact --nocapture
```

Run it with one job and the existing shared target. Failure is a valid first
measurement; do not replace the cumulative caller allowance for that run.
After repair, require that same test to pass. Select existing source-resource
image/owner/import/cleanup and independent Core regressions around the changed
component, plus meaningful exact/short/spent/fresh and mutation controls.
Formatting, targeted Clippy, changed Markdown links/authority and retained raw
receipts accompany the final candidate. No old F-core receipt transfers.

## Discoveries

[Three red measurements](evidence/source-resource-startup-budget/README.md)
localize refusal to strict capture control analysis. Template admission uses one
fresh registry check and two session hits; main reconstruction completes at 207355.
Final Core's registry, graph, owner, byte/window and scope checks complete before
the capture query exhausts the remaining allowance. Capture graph construction
itself completes. The first repair removes an exactly duplicated same-call builtin check by
populating the existing omitted-formal provenance immediately after its one
complete authentication. This saves 15536 units and preserves both provenance
controls. Const-derived expected coordinates then remove repeated scans of the
compiler-owned builtin string, preserving live original checks. The instrumented
startup passes at 318794/327680. Broad probes are removed; a fresh delivered-source
run reproduces that result. Coordinate, builtin, original-provenance, owner,
import, capture and host controls and Clippy pass on the same frozen source inputs.
The image suite is 15/16: dependent-discard reconstruction still refuses with
`Resource`. An exact retained-a301 archive shows this test already failed with bare
`Resource`; the candidate reports `Validation(Resource)`. Internal failure phases
are not claimed equal. The comparison retains source/configuration equality and
its path difference. The
[final evidence](evidence/source-resource-startup-budget/README.md#delivered-source-verification)
retains both results. A separate follow-up under this task and issue #91 must
repair that dependent case before whole-task acceptance; F-core remains pending.

Existing session reuse is bound to exact immutable registry/source/module/global
and unused-ordering-footprint context; conditional, provider and lexical contexts
deliberately require separate admission.

## Deviations

None. A semantic or architectural gap returns to its governing artifact rather
than becoming an allowance increase or local permission.

## Remaining dependent-discard slice

PR #92 retained the bounded original-startup repair at
`f6a2647a03a2172823f38e332c744eba5edeed06`; its independently audited partial
acceptance keeps this task and issue #91 open. Start this slice from that exact
commit in the same worktree. The named dependent-discard test reconstructs
separate Parent and Child template contexts and final copied scopes without
native execution. The earlier baseline establishes an existing named failure;
it does not establish that its bare `Resource` arose in the candidate's later
`Validation(Resource)` phase.

1. Open an individual draft PR before long implementation. Measure decode,
   expected-fact authentication, original template admission, main reconstruction
   and final independent Core on the current test's unchanged cumulative default
   of 327680. Record failures as well as completed phases. Keep optional probes
   test-only and preserve the original result and meter.
2. Measure repeated declaration-coordinate work and context-specific checks
   before selecting a repair. Parent/Child registries, original forests and copied
   substitutions retain their independent authority. Reuse only demonstrated
   context-independent work within an immutable operation; no broader proof cache,
   scheduling change, limit increase or prior-context acceptance transfers.
3. Require the complete image filter to pass 16/16, including dependent-discard
   and the original imported-buffer default test. Retain exact/one-short/prefix/
   retry and tamper/context controls, plus affected owner/import/capture and
   Clippy checks on the final delivered inputs. Remove broad disposable probes
   before the final fresh verification.
4. Obtain independent exact-head review and GitHub squash/merge retention with
   exact tree/ref and acceptance readback. Whole task and F-core acceptance remain
   pending until their original obligations are met. Nominal/resource work waits
   for this repair.

The [initial dependent measurement](evidence/dependent-source-resource-startup/README.md)
completes both original templates at 243110 and reaches final Core at 256303.
Final pre-capture checks complete, then strict capture exhausts the unchanged
caller allowance. Separate template sessions each correctly authenticate their
registry, but each repeats pure source-coordinate extraction costing 9172 and
20442 units. This is measured candidate duplication, not a reusable registry or
forest proof; no dependent-case repair or acceptance follows yet.
