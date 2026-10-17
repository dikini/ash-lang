# TASK-0041: ffi-ash milestone closure

- ID: `TASK-0041`
- Status: active
- Related: [CP-0022 transition history](https://github.com/dikini/ash-lang/blob/adddeffe5d135bd03bf5fc30051965e5da70ed24/docs/proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [GitHub issue #7](https://github.com/dikini/ash-lang/issues/7)

> This task organizes authorized work. It does not define Ash semantics.

## Dependencies

Complete issue outcomes #2–#6 verified on integration/ffi-ash, with unsigned
explicit merges and receipts. The final Main integration gate remains separate.

## Work

1. Review complete implementation/specification correspondence, generic boundaries,
   library migrations and unsupported feature documentation against the
   [implemented profile](../../spec/static-semantics.md#source-foreign-declarations).
2. Consolidate reproducible native build/run instructions and reusable exact-pinned
   positive/negative/lifecycle/control evidence without duplicate fixture corpora.
3. Run the full architecture/workspace gate on the integrated milestone branch;
   resolve regressions before opening the final Main delivery PR.
4. Link issues, tasks and delivering PRs. Close issues explicitly only after complete
   outcomes have retaining-branch verification receipts.
5. After complete checkpoint evidence closes, remove the accepted proposal and
   completed implementation tasks/plans from the product branch and repair their
   current-tree links before the final Main PR. Preserve delivering history links.
6. After the separate Main gate, preserve histories with a signed explicit merge,
   verify integrated Main and close the milestone and this task. Remove the clean
   checkpoint worktree/ref only after proving retaining ancestry under AD-0011.
   Protect paused Lean/Core workstreams.

## Progress

Assignment, blockers, live progress and PR status belong to the linked GitHub
issue. This task retains scope, ordered work and durable implementation findings.

## Verification

Run cargo xtask verify with one Cargo job on the integrated delivery and again
where merged changes warrant it. Check changed documentation metadata, authority,
relative links, Markdown and formal notation. Require generated-host static/shared
execution for all three libraries, separate C mismatch checks, independent Core
rejection, actual native lifecycle, copy/control/quarantine evidence and migration
commands. Final PR contains implementation, normative updates, libraries and
reproducible instructions; no Main integration before that gate.

## Discoveries

### Completing the generated-host linkage matrix

The remaining cells were shared Arena and genuine static SQLite. The existing
Arena harness now selects static or shared fixture linkage while keeping the
same complete Ash scenario, negative-input probes, observations and exact
release identities/order. Its shared child receives a local loader path. Real
allocation and first-allocation injection remain separately labelled; injection
does not demonstrate physical allocation exhaustion.

The SQLite harness keeps shared linkage as its default and runs the entire
unchanged copying fixture through an explicitly supplied implementation archive.
The official 3.46.1 ZIP and header match the existing provenance pins; extracted
`sqlite3.c` has SHA-256
`6c35bc5f7f85eac9c49928bacbb02bb694b547aabf69197e058cca245ad80e83`.
The recorded native build uses `cc -O2 -fPIC` and `ar`, with no SQLite macro
overrides. Archive and executable define the checked `sqlite3_*` implementation
symbols; the generated host has no SQLite `DT_NEEDED` entry. The full copying
result retains integer, Unicode, bytes, empty/NULL and embedded-NUL distinctions.
Static SQLite leaves the executable's platform Rust/libc dependencies intact.

The first focused observation passes both new cells under unchanged work,
stack, depth and admission policies. Each host is built after Ash source removal
and executes after its external image/facts files are removed. Acquisition/build
inputs and generated artifacts have separate roles and pins; the 108 explicitly
named external files include the genuine archive bytes, source/header/object/ZIP
and the added symbol-inspection tools. Before/after effective input records are
equal. Missing `ASH_SQLITE_STATIC_ARCHIVE` is an explicit test failure.
[Reproducible commands](../tools/ash.md#generated-host-linkage-checks) describe the
native input and standalone execution boundary. Full affected owning-target and
quality results, independent review and retention have separate scopes; the
completed PR #41 contribution is recorded below. The next final checkpoint,
issue #7 and Main remain pending.

Prepared declarations and historical experiment passes do not establish product
completion. A receipt pins exact source/configuration and distinguishes executed
properties, foreign assumptions, calibration deficits and unproved properties.

### Transition artifacts and the final closure checkpoint

[PR #41's retained verification](https://github.com/dikini/ash-lang/pull/41#issuecomment-6231289556)
closes the two generated-host linkage cells on `integration/ffi-ash`. The
completed source/Core, program-build/verifier, native-buffer and SQLite tasks
leave the current tree with CP-0022. Their exact historical records remain:
[TASK-0036](https://github.com/dikini/ash-lang/blob/adddeffe5d135bd03bf5fc30051965e5da70ed24/docs/tasks/TASK-0036-source-contracts-core-and-generic-execution.md),
[TASK-0037](https://github.com/dikini/ash-lang/blob/adddeffe5d135bd03bf5fc30051965e5da70ed24/docs/tasks/TASK-0037-program-build-and-interface-verification.md),
[TASK-0038](https://github.com/dikini/ash-lang/blob/adddeffe5d135bd03bf5fc30051965e5da70ed24/docs/tasks/TASK-0038-ash-native-buffer-library.md)
and [TASK-0040](https://github.com/dikini/ash-lang/blob/adddeffe5d135bd03bf5fc30051965e5da70ed24/docs/tasks/TASK-0040-ash-copying-sqlite-library.md).
The specification, accepted decisions, libraries and tool guide retain the
implemented profile; historical partial findings keep their original scope.

This task remains active. [TASK-0042](TASK-0042-rust-verification-performance.md)
and its [execution plan](rust-verification-performance-plan.md) also remain
active and partial. Their controlled old/revised timing comparison is unassigned
and unproved; artifact retirement supplies no benchmark or speedup evidence.
Keep the active product checkout, compatible cache and live verification inputs
until their owners release them under AD-0011.

The next named checkpoint is the final ffi-ash closure and pre-Main preparation
gate. After this cleanup candidate is coherent and receives targeted review, the
sole author runs all seven normal `cargo +1.97.1 xtask verify` stages with no
receipt reuse and one Cargo job. Supply `ASH_SQLITE_STATIC_ARCHIVE`, name all
108 native/source/tool inputs explicitly, and retain the four Rust tool file
pins. Preserve the current work, stack, depth and admission policies. The actual
full-gate receipt and candidate review precede preserving integration and
retained acceptance of this package. Issue #7 and the signed Main integration
gate remain separate.

## Deviations

The execution instruction requires unsigned milestone commits/merges and a
signed final merge into Main. This changes Git signing policy only.

Return concrete semantic gaps to the proposal/design workflow instead of
resolving them locally. Keep excluded features outside this task.
