# TASK-0030: Implement Narrow Checked Foreign Provider

- ID: `TASK-0030`
- Status: active
- Related: [CP-0020](../proposals/CP-0020-narrow-checked-foreign-provider.md),
  [execution plan](narrow-foreign-provider-execution-plan.md),
  [partial evidence](../design/effect-ash/narrow-foreign-provider-evidence.md),
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
  one README admission-status overstatement. That checkpoint did not yet connect
  the owner to the evaluator.
- Compiler admission, exact types/rows, sealed authority and independent linked/
  Core validation are retained at `3d80fbc`. Parent verification passed 23 native
  compiler integration tests, 9 internal authority/restoration tests and strict
  Clippy. Independent contract and quality reviews passed after test-first fixes
  for allocation-failure continuation and restored Success projection.
- Runtime implementation is underway. Eight execution fixtures were observed red
  at the intentional runtime guard. Interaction fixtures cover cleanup, capture,
  recursive discard, mixed owners and outside-owner/running-action rejection.
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

Runtime acquisition, access and ordinary closing pass their focused tests, but
contract review found an internal-teardown prerequisite. Captured continuation
flattening can grow a vector before releasing later native owners. Environment
and type destruction can also allocate before failure returns to the machine;
an owner-first machine destructor alone does not establish the then-accepted
allocation-independent release guarantee. Two independent reviews confirmed
that narrowing this guarantee requires an explicit proposal decision.

An experimental allocation-free frame rotation was rejected: 128 nested frames
required 8,256 visits. No quadratic disposal, general ownership framework or
ownership-representation rewrite is accepted. Shared fallible worklists in the
existing disposal traversals are being implemented under the amendment below.
Refusal-delivery and teardown failure tests remain the evidence gap.
Specification edits are drafts awaiting full contract
implementation and verification, not a retained product checkpoint.

### Accepted failure-boundary amendment

The user accepted fail-stop handling of detectable runtime resource failure in
place of unconditional allocation-independent teardown. CP-0020 now records
distinct capacity, allocator and work-budget causes, phase information, bounded
diagnostics, preservation of original and teardown failures, and explicit
cleanup-completion status. No recovery, retry, limit increase or source cleanup
is permitted after runtime failure.

Native allocation refusal remains recoverable only as an atomic failed attempt
after initializer effects and runtime preparation: no new observable state or
authority, and no further allocation to deliver the prepared failure. Earlier
effects remain committed; the enclosing effect row need not contain allocation
alone. The previous proposed teardown prerequisite is superseded. Implementation
and tests must follow the amended contract; no general ownership framework is
authorized. The old zero-growth test is not evidence for the revised contract
and must be replaced by explicit failure detection and fail-stop evidence.

## Deviations

The user accepted the failure-boundary amendment recorded in CP-0020. Further
semantic gaps still return to proposal review rather than local code decisions.
