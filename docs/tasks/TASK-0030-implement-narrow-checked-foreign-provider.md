# TASK-0030: Implement Narrow Checked Foreign Provider

- ID: `TASK-0030`
- Status: active
- Related: [CP-0020](../proposals/CP-0020-narrow-checked-foreign-provider.md),
  [execution plan](narrow-foreign-provider-execution-plan.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [AD-0001](../decisions/AD-0001-implementation-environment.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

CP-0020 was accepted on 2026-09-08. The user authorized implementation under
the active thread goal. The base is `e20b3ad`, retaining reliable cleanup and
the accepted proposal on `integration/effect-ash-foundations`.
Work uses `.worktree/narrow-foreign-provider` on `codex/narrow-foreign-provider`.
Commits and local integration remain unsigned. No push, tag or main merge.

## Work

Implement the complete CP-0020 contract with one private C allocation bridge,
one fixed builtin API and the existing resource carrier and cleanup machinery.
Keep library-defined acquisition, general FFI and file-specific rules deferred.
The ten-unit milestone forecast is a scope weight, not token or time accounting.
Use bounded subagent tasks, medium reasoning for isolated mechanical work and
high reasoning for authority, ownership and independent review; do not exceed high.

## Progress

- Accepted proposal retained at `e20b3ad`.
- Isolated worktree created; baseline workspace tests passed: 2,545 top-level
  tests plus 8 subprocess tests, log `/tmp/ash-foreign-baseline-20260908.log`.
- Compiler boundary mapping complete. The isolated native owner has 6 passing
  package tests, strict Clippy, rustdoc and ARM64 compile checks. Independent
  contract and high-reasoning unsafe/code-quality reviews passed after correcting
  one README admission-status overstatement. It is not yet connected to the evaluator.
- Contextual designator projection and cell-only import rejection are implemented;
  19 focused syntax/module tests plus the import-authority negative pass.
  Three execution tests remain red at `module.unknown-builtin`.
- All FOREIGN-01 through FOREIGN-10 evidence obligations remain open.

## Verification

The execution plan maps implementation steps to every CP-0020 evidence row.
Each behavioral increment needs a failing test, its minimal implementation and
a passing focused check. Completion requires independent contract and code
quality reviews, full `cargo xtask verify`, Markdown and local-link checks,
retained evidence, specification updates and clean unsigned local integration.
Repeat full verification on the merged integration checkout before removing
the clean, merged feature worktree. Preserve main's unrelated changes and pins.

### Target matrix

| Target | Routine evidence here | Release obligation |
| --- | --- | --- |
| Linux x86-64, eight-bit bytes | Native bridge and full workspace tests on this host. | Retain native results. |
| Linux ARM64, eight-bit bytes | Installed Rust target permits `cargo check --workspace --all-targets --target aarch64-unknown-linux-gnu --locked`. No cross C linker or ARM64 execution host is currently available. | Run native bridge and workspace tests on ARM64 before claiming native platform conformance or releasing there. |
| Other platforms | No provider support claim or simulated fallback. | Explicit support declaration and matching evidence before enabling the bridge. |

The ARM64 compile check is not native execution evidence. This staging does not
remove AD-0001's ARM64 requirement. The bridge is first-party runtime code;
record its unsafe and system-linking boundary without adding an external crate
unless a concrete need is established and reviewed.

## Discoveries

The existing resource frame owns an integer directly; handles and lexical
instantiation already retain a separate activation key. Reuse that distinction
for native storage instead of introducing another identity or owner registry.

## Deviations

None. Return semantic gaps to CP-0020; do not settle new semantics in code.
