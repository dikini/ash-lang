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

## Deviations

None. This delivery removes no semantic, negative, native or stress tests and
changes no production work, depth or stack limit.
