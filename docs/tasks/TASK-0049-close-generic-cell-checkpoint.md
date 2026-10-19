# TASK-0049: Close the Generic Cell Checkpoint

- ID: `TASK-0049`
- Status: active
- Related: [CP-0023](../proposals/CP-0023-scoped-generic-cells.md),
  [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md),
  [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md),
  [TASK-0047](TASK-0047-generic-cell-execution-and-completion.md),
  [TASK-0048](TASK-0048-generic-cell-integrated-verification.md),
  [DN-0053](../design/DN-0053-scoped-generic-cells-without-native-owners.md),
  [DN-0054](../design/DN-0054-base-lexical-region-memory-contracts.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

The user accepted CP-0023 and requested its implementation task breakdown.
The accepted proposal governs every task below; its 31 cases and all their
variants remain required. The ash-ffi baseline is `ffi-base`, peeled commit
`354c76b391fe4af665cf6a03479a9874a57cb3e3`. The checkout recording these tasks
contains older product code. Implementation must use the baseline or an
identified descendant and preserve intervening work; do not infer product truth
from the planning checkout or reset another task's work.

Before implementation dispatch, the coordinating owner records the actual
product head, retaining branch, developer/reviewer assignments, build operator
and integration permissions here or in a linked authorized handoff. None is
assigned by accepting the proposal alone. These tasks do not reopen or declare
complete any existing ash-ffi verification or integration obligation.

DN-0054's region creation, allocation contexts, reservation/local initialization,
storage representations and reclamation remain separate design work. They are
neither a prerequisite nor part of this checkpoint. Cell resource-scope lifetime,
strict retained-payload ordering, resource-cycle rejection, payload-crossing and
native retained-owner protections remain the accepted boundaries.

### Readiness and publication

| Step | Required handoff | What it enables |
| --- | --- | --- |
| TASK-0045 foundation | Reviewed canonical family, typed acquisition, authenticated carrier/summary structure and ordinary validation; exact retained commit and remaining restrictions | TASK-0046 dependency checking and TASK-0047 runtime development |
| TASK-0046 and TASK-0047 connection | Independent dependency admission plus correct runtime transitions on the same carrier, with charged preparation | Public-path acceptance observations across all positive and negative cases |
| TASK-0048 integrated evidence | Adversarial validation, budgets, capacity and real native compatibility results on the connected candidate | Complete checkpoint review and fresh full gate |
| TASK-0049 checkpoint | All case receipts, complete matching specification, independent review and full verification at pinned inputs | Product-checkpoint retention and artifact cleanup under AD-0011 |

Foundation readiness is not task acceptance. TASK-0045's positive execution
criteria may remain open while TASK-0046/0047 proceed; this creates no dependency
on TASK-0045's final completion. Shared elaboration/Core writers and heavy builds
must be coordinated rather than assumed independent.

No staged implementation may publish a checked module, helper summary or Core
permission that relies on unvalidated generic-cell dependencies. Unsupported
paths must fail closed at admission, not merely at execution. Public execution
requires both independent dependency validation and the corresponding runtime.
Each layer owner implements its charging, preflight and iterative disposal as
part of that layer; TASK-0048 verifies these obligations together.

### Acceptance ownership

The primary owner retains each case's complete evidence and acceptance update.
Supporting tasks supply results without duplicating or weakening the case.
The table is a traceability map, not a replacement for CP-0023's semantics.
All entries are pending at task creation.

| Case | Primary task | Required supporting boundary |
| --- | --- | --- |
| CELL-P01 | [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md) | TASK-0047 execution, sharing and initializer multiplicity |
| CELL-P02 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | TASK-0047 old/new snapshot observations |
| CELL-P03 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | TASK-0047 nested lifetime and returned outer access |
| CELL-P04 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | TASK-0047 independent function result after replacement |
| CELL-P05 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | TASK-0047 distinct activations, result and release counts |
| CELL-P06 | [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md) | TASK-0046 imported relationships and TASK-0047 alias behavior |
| CELL-P07 | [TASK-0047](TASK-0047-generic-cell-execution-and-completion.md) | TASK-0046 intercepted retention and reply dependencies |
| CELL-P08 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | TASK-0047 actual handler replies and permitted use |
| CELL-P09 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | TASK-0047 permitted payload crossings and resumption |
| CELL-P10 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | TASK-0047 immutable cyclic values and sharing |
| CELL-P11 | [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md) | TASK-0046 monomorphic dependencies and TASK-0047 legacy coexistence |
| CELL-P12 | [TASK-0047](TASK-0047-generic-cell-execution-and-completion.md) | TASK-0046 contents updates through the other handler |
| CELL-P13 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | TASK-0047 independent reply after dependent mutation |
| CELL-N01 | [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md) | Ordinary phase and diagnostic precedence |
| CELL-N02 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | Hidden/imported/evidence escape and independent Core proof |
| CELL-N03 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | Self-retention despite an identity-free arrow |
| CELL-N04 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | Indirect cycle and later-clear rejection |
| CELL-N05 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | Younger/incomparable owners and unsafe joins |
| CELL-N06 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | Later read and handler-reply escape |
| CELL-N07 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | Request payload, evidence and indexed metadata crossing |
| CELL-N08 | [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md) | Scope rejection and valid shadowing companion |
| CELL-N09 | [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md) | Canonical family/evidence authentication |
| CELL-N10 | [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md) | Monomorphic read and rank-1 restrictions |
| CELL-N11 | [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md) | TASK-0048 ash-ffi restricted-value regressions |
| CELL-N12 | [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md) | Stateful P13 handler followed by dependent builtin read |
| CELL-C01 | [TASK-0047](TASK-0047-generic-cell-execution-and-completion.md) | TASK-0046 ownership proof and TASK-0048 malformed-key probes |
| CELL-C02 | [TASK-0047](TASK-0047-generic-cell-execution-and-completion.md) | TASK-0046 discard/cleanup proof and initializer capture |
| CELL-C03 | [TASK-0048](TASK-0048-generic-cell-integrated-verification.md) | TASK-0045/0046 ordinary and dependency validation; TASK-0047 observations |
| CELL-C04 | [TASK-0048](TASK-0048-generic-cell-integrated-verification.md) | TASK-0045/0046/0047 owning ledgers and failure boundaries |
| CELL-C05 | [TASK-0048](TASK-0048-generic-cell-integrated-verification.md) | TASK-0046 finite analysis and TASK-0047 capacity/disposal |
| CELL-C06 | [TASK-0048](TASK-0048-generic-cell-integrated-verification.md) | All implementation owners and actual generated native host |

## Work

1. Maintain readiness handoffs and case receipts on pinned implementation
   commits. For each case record exact fixtures/test names, expected and actual
   result or phase/reason, direct/imported/transformed variants where required,
   owning task, review and retained commit. Keep partial criteria unchecked.
   Before removing transition artifacts, retain the complete case map, results,
   measured limits and checkpoint receipt in
   `docs/design/generic-cell/evidence.md`, with pinned historical links to the
   governing proposal and tasks. Consolidate durable conclusions there; raw logs
   remain working records under the documentation policy. Required receipts must
   survive disposable build-cache cleanup. The evidence record reports verified
   behavior and does not define semantics.
2. Reconcile specification changes from TASK-0045–0047 across `spec/syntax.md`,
   `spec/name-resolution.md`, `spec/static-semantics.md`, `spec/elaboration.md`
   and `spec/dynamic-semantics.md`, including diagnostics and failure boundaries.
   Update affected public tool/library documentation and executable examples
   from verified implementation. No normative change is made by this planning
   task before implementation.
3. Confirm all 31 cases, all compound variants and preserved legacy/native
   obligations, with connected evidence from TASK-0048. Review publication,
   budget and independent-validation boundaries as well as observed values.
4. Arrange independent review and one fresh full verification gate after the
   connected implementation, specification and focused evidence are ready. The
   coordinating owner of this task owns that next checkpoint and assigns one
   build operator. Preserve exact-input receipts and distinguish focused,
   complete-gate and retained-result claims.
5. Retain the complete product checkpoint with implementation, tests,
   specification, review and verification. Apply/read back the task acceptance
   updates using the retained receipt. Only then remove CP-0023 from the product
   branch and retire completed task/plan artifacts under the artifact guide and
   AD-0011, repairing indexes and links. Git retains the transition evidence.
6. Main integration remains its separately authorized gate. Before that
   integration, require a fresh full gate on the pinned candidate, or transfer
   the checkpoint gate only when its inputs remain identical. Verify the actual
   retained result and do not call the transition current before integration.

## Progress

### TASK-0045 launch, 2026-10-19

- Product base: `67ba281d4e93dbfad65e5fd1e6a34c3dfb132686` (`origin/main`
  as locally recorded), a descendant of `ffi-base`.
- Accepted planning artifacts: copied from
  `3e6326390cb182b211328682df9591d5c0311fc3` without merging the older product
  implementation from that planning branch.
- Product checkout: `.worktree/generic-cells`; retaining checkpoint branch:
  `codex/generic-cells`.
- Coordinator and acceptance owner: `/root` in the launching chat.
- Developer and sole heavy-build operator: `/root/task0045_developer`, requested
  and dispatched as `gpt-6.1-sol` with `medium` reasoning effort.
- Independent reviewer: `/root/task0045_reviewer`, with inherited model/effort.
  The reviewer does not author implementation and coordinates any build reruns.
- Local commit policy: unsigned commits, using `git -c commit.gpgsign=false commit`;
  no push or Main integration.
- Authorized scope: TASK-0045 foundation implementation, required tests and
  specification/task updates, local commits and repair/re-review. Review must
  finish before any advance to TASK-0046/0047. No Main integration is authorized.
- Next full gate: the connected generic Cell product checkpoint described
  below; TASK-0045 uses focused checks and independent review. Criterion-specific
  and full-checkpoint acceptance remain distinct.

TASK-0045 retains its foundation candidate locally at
`752b69cdb909c66f6810cec4709aa06fde44b2e8`. Its
[verification record](TASK-0045-generic-cell-api-and-acquisition.md#foundation-verification-record)
pins focused tests, ordinary authentication, staged publication restrictions
and the remaining dependency/runtime evidence. Independent code re-review is
clear, and its independent technical evidence verdict has no unresolved
findings. The coordinator accepted foundation readiness only. All 31 case
criteria and complete checkpoint acceptance remain open. TASK-0047 and
TASK-0048 have not been dispatched. DN-0054 remains byte-identical; no region
implementation is included.

TASK-0046 is authorized from reviewed local commit
`77032c7659278a49a80dc736497649e563ec2dd9`, using the same product checkout and
retaining branch. `/root/task0045_developer` remains sole writer/build operator
with requested/effective `gpt-6.1-sol` and `medium` effort;
`/root/task0045_reviewer` independently reviews and `/root` owns acceptance.
Exact model runtime is unavailable. All local commits remain unsigned using
`git -c commit.gpgsign=false commit`. No push, Main integration, TASK-0047
implementation/dispatch or DN-0054 changes are authorized. TASK-0046 delivers
all assigned dependency-checking obligations; required runtime observations
remain pending TASK-0047, integrated evidence TASK-0048 and the fresh full gate
this checkpoint. Source admission must not grant generic execution readiness.

### TASK-0046 resumed handoff, 2026-10-19

The resumed developer and sole product writer/Cargo operator is
`/root/task0046_developer`, dispatched as `gpt-6.1-sol` with `medium` effort;
exact model runtime is unavailable. `/root/task0046_reviewer` independently
reviews and `/root` retains coordination and acceptance ownership. The earlier
TASK-0045 assignments above are historical and remain unchanged. The checkout,
retaining branch, unsigned-only commit policy and authorization exclusions stay
the same. The pre-pause whole-library process was cancelled (exit 130); absent
old temporary logs supply no transferred final receipt.

TASK-0046's [resumed dependency record](TASK-0046-generic-cell-contents-and-dependencies.md#resumed-dependency-delivery-2026-10-19)
pins code commit `3f72e9ce3a1822631eb94762dbe1f6c0bde1806c`, its exact input
records, fresh focused commands/results and the identical-file Clippy transfer.
It maps all fifteen assigned families to paired source/import/Core evidence and
records the stack, exact-handler, diagnostic and private-phase repairs. This is
a dependency-readiness handoff accepted by the coordinator at that code pin.
All original TASK-0046 case criteria and all 31 checkpoint cases, including every
compound variant,
remain open pending their complete observations.

Next owners remain TASK-0047 for runtime transitions, results, sharing and
release counts; TASK-0048 for the connected adversarial, budget, capacity and
native matrix; this task for matching specification, case receipts, independent
checkpoint review and the fresh full workspace gate. TASK-0047 has not been
implemented or dispatched by this handoff. Generic source/Core admission still
grants no evaluator/build execution permission. Scope lifetime, strict owner
ordering, resource-cycle rejection, outward payload crossing and native
retained-owner rules remain fixed. DN-0054 is unchanged and no region mechanism
is included. No push, PR, Main integration or cleanup is authorized here.

### TASK-0047 connection authorization, 2026-10-19

The user authorized the prerequisite TASK-0047/0048/0049 work needed to complete
original TASK-0046 acceptance. This supersedes the earlier TASK-0047 exclusion
for the new assignment; historical launch/receipt restrictions remain recorded
as they applied then. Start from clean retained head
`ee306d161478d2b135c503d7b79056f8b0dfa32b`, with tested dependency code
`3f72e9ce3a1822631eb94762dbe1f6c0bde1806c` and reviewed foundation `77032c7`.

`/root/task0046_developer` remains sole product writer and Cargo operator,
requested/dispatched as `gpt-6.1-sol`, `medium`; exact model runtime is
unavailable.
`/root/task0046_reviewer` independently reviews immutable inputs without Cargo;
`/root` coordinates and owns acceptance. Reuse `.worktree/generic-cells`, branch
`codex/generic-cells`, Rust 1.97.1 and its existing target cache, one Cargo job
and `RUSTC_WRAPPER=`. Preserve the planning checkout and concurrent design work.
All local commits remain unsigned; no push, PR or Main integration is
authorized.

The [TASK-0047 plan](task-0047-execution-plan.md) connects the authenticated
carrier to ordinary fixed-type payload execution, completion and owning ledger
probes. Required public P01–P13 and C01/C02 observations include actual values,
distinct recursive activations and release counts. Independent review and
focused verification at a frozen runtime pin precede advancement. Root then
advances TASK-0048's integrated adversarial/budget/capacity/native matrix and
owns TASK-0049's next fresh full `cargo xtask verify` checkpoint after connected
behavior, specification and case receipts are ready. Original compound criteria
remain open until their complete observations exist.

DN-0054 remains separate and byte-identical. No region work, native lifetime
relaxation or private lifecycle expansion is authorized. Worktree/cache
retirement and proposal cleanup wait for the completed product checkpoint.

### TASK-0047 runtime handoff, 2026-10-19

The [runtime connection receipt](TASK-0047-generic-cell-execution-and-completion.md#runtime-connection-2026-10-19)
records P01–P13 actual values, recursive acquisition/release counts, C01 latest
roots, separate C02 initializer/outside/running-completion controls, owning
preflight/disposal boundaries and generated execution after source removal.
The runtime observation pin is unsigned
`8d5b3c125d042901518c9fcc413ad2c48c730382`; the final inventory-test pin is
unsigned `ac72d18623724f399f1f1dfcf3a0046d63669b81`, tree
`7cab3d454aeac34f4e77c3603b382814fa6cef46`.

Only the architecture test's closed inventory changes between these pins.
All other 1761 file modes/contents are exact, preserving
production/configuration
and previously exercised test inputs. TASK-0047 records both frozen manifests,
explicit five-check transfer, fresh architecture/Clippy/formatting receipts,
commands, tool pins and actual log hashes. Current 1762-record SHA-256 is
`11f96a5286ad8290df680b81a89cb5189d58a9f5f2ca74be78b2a78b7b61deed`.

Checks pass: library 1931, resource/cleanup 170, affected/native/build 121,
architecture 47, exact CLI example 1, strict affected Clippy, formatting and
warnings-denied Rustdoc. All eight selected receipts exit zero with stable
inputs at their stated pins; no complete checkpoint gate is claimed.

`/root/task0046_reviewer` cleared code and technical evidence at `ac72d18`.
`/root` accepted TASK-0047 connection readiness subject to the final
receipt-only
retained readback before TASK-0048 advancement. Original TASK-0046 compound
criteria, all 31 primary case records, TASK-0048's
complete matrix and TASK-0049's fresh full gate remain open. Actual deep generic
owned discard remains TASK-0048 C05; normal/replacement/internal-failure payload
disposal and common discard regressions do not supply it. Baseline native
callers passing is distinct from pending real mixed C06. DN-0054 remains
byte-identical. Only task receipt prose changes after `ac72d18`; production,
other tests, specification and configuration stay exact. No Cargo process
remains live; the worktree, cache and useful evidence remain. No push, Main
integration or checkpoint cleanup has occurred.

### TASK-0048 verification launch, 2026-10-19

Root accepted retained TASK-0047 runtime component readiness at unsigned clean
`9cfd39a9a9f82e265cd82bbc73d438dc4968d357`, tree
`0d96a246739bcba2086538798dd3e1a9e3d5816a`, after independent retained review.
The user's existing authorization now advances TASK-0048, using its task-owned
[execution plan](task-0048-execution-plan.md). Runtime observations remain pinned
to `8d5b3c1`, final inventory evidence to `ac72d18`, with scoped input transfers.

`/root/task0046_developer` remains sole product writer/Cargo operator on
`.worktree/generic-cells`, branch `codex/generic-cells`, dispatched as
`gpt-6.1-sol`, `medium`. `/root/task0046_reviewer` independently reviews without
Cargo; `/root` owns acceptance and the following TASK-0049 full checkpoint.
Reuse Rust 1.97.1, one job, `RUSTC_WRAPPER=` and the existing target cache.
Preserve the planning checkout's concurrent design paths and DN-0054 bytes.
No new permission, native lifetime relaxation, private phase expansion, region
implementation, push/PR/Main integration or cleanup is included.

The immediate checkpoint is frozen TASK-0048 connected/adversarial/budget/
capacity/native evidence, independent review and retained readback. Actual deep
generic owned discard and mixed real native quarantine close the named C05/C06
gaps. All 31 original case/variant records remain subject to complete matching
evidence and TASK-0049's fresh full `cargo xtask verify`; focused readiness does
not complete that acceptance.

- [x] TASK-0045 launch records product inputs, retaining branch, roles and
  permissions. Later task dispatches require their own exact input handoffs.
- [x] TASK-0045 foundation enables the downstream work without unchecked publication.
- [ ] TASK-0045–0047 deliver connected behavior and specification changes.
- [ ] All 31 primary case records include every CP-0023 variant and required
  positive, negative, Core, runtime and native observations.
- [ ] TASK-0048 integrated evidence and independent review have no unresolved
  findings or omitted boundaries.
- [ ] Fresh full gate passes at pinned checkpoint inputs; retained result verified.
- [ ] Product acceptance updates, proposal cleanup and index/link repairs are
  retained without prematurely claiming Main integration.
- [ ] Any separately authorized Main integration satisfies its gate and retained
  verification before this transition is described as current Ash.

## Verification

The checkpoint's build operator runs the full default gate on frozen inputs:

```sh
CARGO_BUILD_JOBS=1 cargo xtask verify
```

Use the actual descendant's documented verification command and toolchain;
record any command change rather than silently reusing a historical receipt.
The full gate supplements the case-specific evidence and real native runs; it
does not replace missing assertions. Compare source/configuration/tool/artifact
pins before and after verification and after authorized retention.

Check artifact IDs/status, every case-to-task mapping, relative and pinned
links, Markdown, source example layout, and specification authority. Preserve
DN-0054 separately and confirm no region implementation has entered this scope.
Unchanged old full gates and successful focused tests are not this checkpoint's
fresh complete verification.

## Discoveries

The ash-ffi baseline already has the relevant effect, resource, native retention
and independent Core boundaries. Generic payload contents require additional
flow relationships; they do not require the broader base-region model first.

## Deviations

None authorized. Semantic changes return to CP-0023; tasks cannot relax its
scope lifetime, cycles, positive-case precision, crossing or retention rules.
