# TASK-0042: Rust verification performance

- ID: `TASK-0042`
- Status: active
- Related: [AD-0014](../decisions/AD-0014-rust-verification-stage-reuse.md),
  [AD-0001](../decisions/AD-0001-implementation-environment.md)

> This task organizes authorized tooling work. It does not define Ash semantics.

## Dependencies

The user authorized implementation and coordination with the ffi-ash team.
Use an isolated tooling checkout and target cache. The milestone PM owns the
heavy-build slot; preserve its current frozen gate, review and product checkout.

## Work

1. Preserve default-feature checking and product linkage while avoiding a second
   linked set of integration-test harnesses.
2. Add explicit stage selection and exact-input local successful-stage receipts.
   Keep plain verification fresh and report reuse separately.
3. Test failure and invalidation behavior before measuring the whole gate.
4. Document commands, receipt boundaries, dependencies and workflow ownership.
5. Compare the old and revised plans on frozen milestone inputs in the assigned
   build window, then hand reviewed results to the milestone PM.

The [execution plan](rust-verification-performance-plan.md) belongs to this task.

## Progress

Design accepted through the user's implementation instruction. Coordination
requested; the current milestone gate continues unchanged.

The real-tool partial reuse smoke test initially took 26.47 seconds for two
unchanged stages. Debug receipt hashing was avoidable overhead. The xtask alias
now uses an optimized, tool-only profile; product gate profiles are unchanged.

Independent review of candidate `777aec9` reproduced stale reuse after chmod,
changed PATH native tools masked by overrides, and changed rustup components
behind a fixed launcher. Each gained a failing regression before repair.
File metadata and the actual delegated tools are now pinned. Failed executions
also retain their timing and log in the run summary without a success receipt.
The subsequent repairs were independently re-reviewed. The full comparison
waited for the milestone repair and its assigned build window.

Re-review exposed non-executable PATH shadows and dangling symlink retargeting.
The runner now pins all existing PATH candidates conservatively and records
link identity even when the referent is absent. Named external file inputs
still require readable contents. The comparison harness passed stub-based
smoke checks for identical outer test counts, complete seven-stage reuse and
rejection after inherited Cargo configuration movement.

The same PATH selection pinning now covers bare compiler overrides and both
compiler wrappers. A changed executable behind a non-executable PATH shadow
cannot reuse the wrapper's earlier success. All 17 focused regressions, strict
xtask Clippy and xtask rustdoc pass. Independent review cleared tooling candidate
`aadd4be` after adversarial probes of permissions, overrides, rustup delegation,
PATH shadows, symlinks and both wrappers.

[Draft PR #18](https://github.com/dikini/ash-lang/pull/18) contains the reviewed
implementation. The milestone PM assigned the serial old-six, revised-seven
and explicit-reuse comparison to its sole build owner on product candidate
`dd3239e`, with the same seven-file tooling overlay in both fresh plans.
Product target metadata is unchanged: 134 targets, with two overlaid xtask
targets and 17 tooling tests accounted for separately. Real formatting/metadata
smoke checks took 11.74 seconds fresh and 2.23 seconds reused; these are partial
checks, not full-gate measurements.

The first comparison attempt exhausted temporary storage during the old build.
Its logs and cache were preserved and excluded. A second attempt completed the
old default build in 906.59 seconds, then was stopped because the measured
debug-artifact footprint made two retained caches unsafe on the project disk.
That partial attempt is also excluded. The PM assigned a new serial comparison
on a separate filesystem with enough capacity, fresh caches and new input
records. Complete gate times, matching per-target test counts and the final
handoff are pending. On that candidate, the altered root manifest/lockfile
changes the runtime identity; original-configuration native/image evidence
remains a separate requirement.

The third attempt completed the old default build in 731.34 seconds and Clippy
in 135.52 seconds, then stopped on a failing source-formula owner guard in
`method_parameter_resources`. Its three expected strings omit spelling charges
retained by the owning unit probes. The test stage exited 101 after 1,482.94
seconds; only 69 of 136 outer targets were reached. Independent review
authenticated all five completed stage logs and unchanged input/tool pins.
Documentation, revised fresh and reuse stages did not start. This failed
partial attempt establishes no complete gate or before/after result. The PM
assigned focused diagnosis using the existing cache.

The subsequent three-string repair reused that same checkout and target path.
Its affected test target compiled in 2.86 seconds (Cargo-reported), and the
command passed all four tests in 4.29 seconds wall time. The three owning unit
probes each passed in under one second command wall time. These are focused
repair results, not a full-gate comparison; they demonstrate the edit loop with
compatible cached artifacts rather than a new cold build.

The edit-loop guide now selects packages, targets and cases explicitly and
distinguishes fresh verification from cold compilation. Suitable checkouts and
compatible caches are reused, with one writer per product cache. Superseded
failed caches can be reclaimed after preserving evidence and confirming no
active owner needs them. The user also requested measurement of the compilation
cost itself. Reduced debug information is a later controlled experiment;
existing gate profiles, limits and tests remain unchanged here.

After the sole owner confirmed no remaining dependency and independent review
checked the deletion scope, the two excluded storage-failed caches were retired.
Their 78.43 GB allocated footprint was removed; measured free space increased
by 78.42 GB (73.03 GiB). Interruption logs/receipts, file metadata inventories,
Cargo fingerprints, dependency records and referenced build outputs were
preserved outside the caches. The active comparison cache, product checkout,
shared caches and other worktrees were untouched. The user accepted reuse of
one sequential product checkout with target caches retained across branch
switches; [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md) and the
[agent guide](../project/agent-workflow.md) now record that workflow.

## Dependencies introduced to xtask

These are development-tool dependencies already resolved and used by Ash.
`Cargo.lock` changes only xtask's dependency edges; no package version or
checksum changes. The standard library provides neither SHA-256 nor typed JSON
receipt encoding. Reusing existing packages avoids custom cryptography and a
second serialization format. They enter the local xtask executable, not a new
Ash runtime or foreign ABI artifact.

| Package | Requirement / resolved | Purpose | Source |
| --- | --- | --- | --- |
| serde | `1` / `1.0.229`, derive | Typed local receipts | [serde-rs](https://github.com/serde-rs/serde) |
| serde_json | `=1.0.151` | Receipt encoding | [serde-rs/json](https://github.com/serde-rs/json) |
| sha2 | `=0.10.9` | Input and log hashes | [RustCrypto](https://github.com/RustCrypto/hashes) |

All three declare `MIT OR Apache-2.0`. Their maintained source repositories,
local registry sources and resolved transitive graph were inspected. The graph
is serde_core/derive, proc-macro2, quote, syn, unicode-ident, itoa, memchr, zmij,
cfg-if, cpufeatures, digest, block-buffer, generic-array, typenum, crypto-common
and version_check. Licenses are MIT or Apache-2.0, except generic-array/zmij
(MIT), memchr (Unlicense or MIT) and unicode-ident (MIT or Apache-2.0 **and**
Unicode-3.0). Retain the selected license notices and the Unicode notice as
applicable. Ash's unspecified license prevents a final compatibility claim.

The packages expose portable Rust APIs; this delivery targets Linux x86-64 and
the pinned Rust 1.97.1. Serde/JSON require Rust 1.56/1.71 respectively; resolved
declared minimum versions do not exceed 1.71. SHA-2 selects target-specific CPU
features internally. Other target builds remain unmeasured. The runner requires
Git and UTF-8 file/environment names; shell fixture tests run on Unix.

First-party xtask forbids unsafe code through workspace lints. Dependency
inspection found UTF-8 and numeric formatting fast paths, proc-macro token
internals, array/slice layout casts, and CPU intrinsic/feature dispatch in the
resolved graph. These stay behind existing safe dependency APIs; no new unsafe
call or optional assembly feature is enabled. This is a source/role review,
not an independent dependency audit.

`cargo audit --no-fetch` against local database commit
`bf5c0d245a92671908518d7e765914d437954ed6` (2026-08-21) found zero
vulnerabilities in the workspace graph. Its informational warning for the
unrelated crates.io Vulkan package `ash` does not apply to this local Ash
package. The database date bounds this observation. Published SHA-2 advisory
[RUSTSEC-2021-0100](https://rustsec.org/advisories/RUSTSEC-2021-0100.html)
does not affect the resolved 0.10.9 release. Full workspace verification with the
changed lockfile remains part of the assigned comparison gate.

## Verification

Run the xtask regression suite, formatting, strict xtask Clippy and rustdoc.
Exercise the real revised full gate and explicit reuse on the frozen benchmark
checkout. Preserve source/configuration equality, output logs, test counts and
wall times. Check changed Markdown links, authority and command accuracy.
Independent review precedes the milestone tooling handoff.

## Discoveries

The old gate builds all targets with default features and tests all targets
with all features. All-feature coverage cannot substitute for default-feature
coverage. Existing milestone retention already transfers a successful gate
through exact tree/input equality and adds fresh connected native observations.

A bounded read-only audit of candidate `dd3239e` found later test-runtime
opportunities: shared immutable source/token views and declaration/site indexes
in `tests/architecture.rs`, and identical-byte linear input generation in
`tests/data_and_adts.rs`. The few `Copy`/exhaustive-match assertions already
enforced by Rust appear cheap. Distinct pipeline routes, resource-failure cases,
small-stack behavior, traces and post-transform validation remain independent
obligations. Historical target totals do not establish savings for any proposed
optimization; those changes and measurements require a later delivery window.

## Deviations

None. This delivery removes no semantic, negative, native or stress tests and
changes no production work, depth or stack limit.
