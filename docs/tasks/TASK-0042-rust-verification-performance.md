# TASK-0042: Rust verification performance

- ID: `TASK-0042`
- Status: active
- Related: [AD-0014](../decisions/AD-0014-rust-verification-stage-reuse.md),
  [AD-0001](../decisions/AD-0001-implementation-environment.md)

> This task organizes authorized tooling work. It does not define Ash semantics.

## Dependencies

The user authorized implementation and coordination with the ffi-ash team.
Continue PR #18 on its existing `codex/verification-reuse` branch in the assigned
product checkout. The milestone PM assigns one heavy-build operator. Reuse the
same compatible target cache and its generated-host child; reviewers inspect
that operator's frozen inputs and evidence. Preserve the active CP-0022
checkpoint, unrelated worktrees and Main drafts.

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

[PR #18](https://github.com/dikini/ash-lang/pull/18) delivers the revised command
matrix, conservative exact-input receipts and temporary generated-host cleanup.
Its existing history now includes retained ffi-ash checkpoint `c2e21cc` through
an unsigned explicit merge. The PR targets `integration/ffi-ash`; Main
integration remains a separate human gate. Candidate `1325097` passed
[independent review and completed-evidence authentication](https://github.com/dikini/ash-lang/pull/18#pullrequestreview-5487833850).
Unsigned checkpoint integration, retained acceptance and closure are the next
gates; their assignment belongs to the milestone PM.

The tooling implementation passed 17 regressions and independent adversarial
review at `aadd4be`. The regressions cover permissions, PATH shadows, dangling
symlinks, compiler overrides, both wrappers, rustup delegation, moved inputs,
failed commands and changed logs. Exact input pins include file metadata and
actual delegated tools. Product profiles, tests and work/depth/stack policies
remain unchanged.

The controlled old-six/revised-seven comparison did not complete. Storage
failures and a source-formula owner guard stopped the earlier attempts; their
revised/reuse legs never ran. The three-string repair preserved the actual
spelling charges and passed its four-test target and three owning probes using
compatible artifacts. PR #17 subsequently retained a successful six-stage gate
under its declared overlay conditions. That gate is historical evidence for
PR #17, not a completed performance comparison or this changed candidate.
The later fresh-seven assessment was interrupted by the human pause before
completion. Its receipts provide neither a full gate nor exact seven-stage
reuse. Modified host source also invalidates those old exact-input receipts.

Generated Cargo roots now retire after the executable is copied and before it
is published. Package-scoped cleanup preserves shared dependencies and current
test artifacts. Link, copy and cleanup failures preserve the existing output
and diagnostic log; a private generated cache is removed completely. Source,
manifest, payload and log records retain their caller-controlled lifetime.

The authorized cleanup patch passed the following connected focused checks on
2026-10-12 in the existing product checkout and cache:

| Operation | Result | Wall seconds |
| --- | --- | ---: |
| Selected compilation | Passed | 128.563 |
| Cleanup unit cases | 5 passed | 3.239 |
| Program-build target | 4 passed | 41.753 |
| Native static/shared and refusal matrix | 1 passed | 6.914 |
| Strict focused Clippy | Passed | 23.223 |

Compilation plus tests took 180.469 seconds; with Clippy, 203.692 seconds.
These are scoped observations, not a causal full-gate speedup. The ten tests
and their input hashes were independently checked. They do not establish the
final candidate's complete gate. The controlled cleanup fixtures retained zero
root files, preserved shared artifact bytes and executed the copied programs.
The connected real-host run retained no new generated roots. Separately,
authorized retirement removed 29 historical generated packages, 589 files and
87 directories, reclaiming 6,600,482,816 allocated bytes. All 21,442 protected
other files and 484 Cargo fingerprints were unchanged. The cleanup bundle and
its receipts remain live review evidence until this PR/checkpoint no longer
needs them.

On 2026-10-12, candidate `1325097` passed one fresh seven-stage gate with seven
stages executed and none reused. Its immediate exact-input functional witness
reused all seven successes and executed no stages. Fresh summaries and logs
were preserved before reuse. The complete 136 outer targets matched metadata:
134 product targets passed 3,671 tests with no failures and one ignored test;
two tooling targets passed 17 tests with no failures or ignored tests. Nine
nested summaries were retained separately and excluded from those totals.

| Measured operation | Wall seconds | Scope |
| --- | ---: | --- |
| Fresh gate runner | 1,026.273 | All seven stages and their input checks |
| Fresh launch | 1,051.218 | Includes the 24.91-second operator compilation |
| Test stage | 827.276 | Includes reported test compilation of 4m27s |
| Documentation stage | 16.081 | Warnings-denied workspace rustdoc |
| Exact reuse runner | 8.045 | Seven stages reused, none executed |
| Exact reuse launch | 8.165 | Includes the invocation around the runner |

Product target execution times sum to 475.53 seconds and tooling targets to
81.86 seconds. These rounded subtimes overlap the test-stage wall; do not add
them to it or equate them with model runtime. Exact LLM runtime is unavailable.
Tool-call, batch and turn wall measurements retain their distinct scopes.

The current native build, source arena, acquired-only and source-owner suites
passed under the candidate's matching compiler/runtime configuration. The
arena, acquired-only and generic program-build fixtures remove Ash sources and
retain payload files. Source-owner and scalar native-build fixtures also remove
image/facts files before child execution. The
default-feature build and subsequent all-feature test runtime identities were
recorded separately. Postgate inspection found zero generated-host root aliases,
dependency files, fingerprints or incremental roots in the scoped shared caches;
shared dependencies and current tests remained available. This observation is
not a new reclaimed-byte measurement.

The [public result and timing receipt](https://github.com/dikini/ash-lang/pull/18#issuecomment-6119984446)
and independent review bound these claims to `1325097` and its frozen inputs.
This task-only summary changes the whole-repository Git input identity. Transfer
requires demonstrated equality of the unchanged executable, compiler,
configuration and native inputs plus independent review; the old whole-input
receipts must not be reused against unequal Git inputs. Manual Markdown, link
and authority checks verify this prose; the reviewer assesses the bounded
evidence transfer.
Neither the fresh gate nor exact reuse supplies the deferred controlled
old/revised comparison or a causal speedup claim. TASK-0042 remains active after
this partial delivery; no ffi criterion is completed by the tooling evidence.

## Operating and cleanup handoff

Use one branch per PR, one physical product checkout and one shared build set.
The developer is the sole writer and Cargo operator; use one job and sequential
checks. Branch switches require released readers, a clean working tree and
preserved owned changes. The current checkout is `.worktree/ffi-ash-contract`;
the cache is `.worktrees/pr11-rereview-target-97287b0`, including its
`ffi-native-hosts` child. No role-specific checkout, branch or cache is needed.
Reviewers inspect immutable evidence and request necessary reruns from the
operator. All agent commits, merges and pushes remain unsigned; the signed
explicit Main merge belongs to the human.

During development, run focused checks for the affected boundary. Run the
required full gate once at the final acceptance boundary. Do not add benchmark
builds, cold caches or documentation builds outside the assigned scope.

Record inspection/dispatch, compile/link, tests/native hosts, documentation,
review, integration/acceptance, cleanup and waiting separately. Preserve model
and effort, tool-call timings and available turn wall time. Exact model runtime
is unavailable unless exposed; a turn wall or elapsed-minus-tools proxy is not
exact LLM time. Parallel tool sums and batch wall time are different measures.
The PM owns the current timing account and the developer supplies scoped
operation receipts; timing collection adds no verification runs.

At closure, consolidate lasting conclusions here and in tool documentation.
Retire obsolete working history and superseded output only after proving that
no live PR/checkpoint needs them. Preserve compatible dependencies, current
tests, published executables and CP-0022 evidence. The developer supplies a
cleanup **Result** and **Next owner**; PM confirms them before starting the next
PR. Current **Result**: the twelve-path transition preserved all owned source;
the candidate's fresh gate, exact reuse and zero generated-root residue are
independently authenticated. Shared caches and live PR/checkpoint evidence
remain retained; historical generated-root retirement is complete. Current
**Next owner**: the reviewer authenticates this task-only successor's evidence
transfer, then the PM assigns unsigned integration and retained acceptance.
Scoped closure cleanup still requires its own Result and Next owner.

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
changed lockfile passed the candidate's fresh gate recorded above.

## Verification

Require the complete fresh seven-stage gate and exact product/tool target
inventory at the final candidate. Retain focused cleanup/tool regressions,
matching native/image observations and independent review as separate claims.
Any immediate reuse witness must report all seven stages reused under equal
inputs, configuration and saved logs; a fallback or mixed run is not that
witness. Check changed Markdown links, authority and command accuracy.

A controlled old/revised timing comparison with comparable cache states remains
required for the whole task. It needs a later explicit scope and operator
window; no new comparison is assigned by this partial delivery.

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

The whole-task controlled timing comparison remains incomplete. This partial
delivery removes no semantic, negative, native or stress tests and changes no
production work, depth or stack limit. The paused assessment and superseded
comparison recipes are not continuation points.
