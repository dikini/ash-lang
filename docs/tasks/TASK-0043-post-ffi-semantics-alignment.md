# TASK-0043: Post-ffi semantics alignment

- ID: `TASK-0043`
- Status: active
- Related: [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [current static semantics](../../spec/static-semantics.md),
  [current dynamic semantics](../../spec/dynamic-semantics.md)

> This task organizes authorized repairs. It does not define Ash semantics.

## Dependencies

The user authorized row-unification repair first, then reconciliation of the
remaining specification/implementation mismatches, with focused regressions,
independent review and separate PRs. Start from Main `354c76b` and the immutable
`ffi-base` tag at that commit. The completed ffi milestone remains complete.
Main integration requires separate human approval.

Use the existing `.worktree/ffi-ash-contract` checkout and compatible
`.worktrees/pr11-rereview-target-97287b0` cache. The developer is the sole product
writer and heavy-build operator; use Rust 1.97.1 and one Cargo job. Preserve the
private primary checkout, all production work/depth/stack limits and unrelated
worktrees and caches.

## Work

1. Repair effect-row unification to satisfy existing unordered, idempotent exact
   instance equality. Add regressions before implementation. Retain choices
   until the enclosing unification succeeds, and roll back failed choices.
2. Honor documented ABI output order while preserving owner, offset, lifetime,
   source/Core/image and native cleanup validation. Correct acquisition wording
   and obsolete overview exclusions in that connected delivery.
3. Restore normative diagnostic precedence and clarify primitive operand heap
   threading. Return any actual semantic gap to proposal/design work.

Each package receives focused verification and independent review. Freeze and
hand off its exact head before starting the next stacked branch.

## Progress

The first delivery uses `codex/row-unification-backtracking` from `354c76b`.
Baseline source probes are retained at
`.worktrees/semantics-alignment-context-20261017/baseline-review`; they identify
the failing generic row, passing concrete/single-member controls and compiler
SHA-256 `8621279869c3c87f297c80406a0bad182651eb382fccec35be60a244d4ea0ebb`.
[PR #44](https://github.com/dikini/ash-lang/pull/44) publishes row repair code
commit `2a4091479f22335dd48343a610765f753703066f` against Main `354c76b`.
Independent review cleared the exact published row head `f077fd4` in
[the PR review](https://github.com/dikini/ash-lang/pull/44#pullrequestreview-5559465031).
The reviewer authenticated fresh 4/4 row-choice and 1/1 exact-budget reruns and
released the frozen reader lease. Retained verification remains pending.

Cleanup Result: the row checkout was clean with no owned scratch to retire;
its live receipts and compatible cache remain needed by the stack. Next owner:
the developer continues the ABI-order package on
`codex/foreign-output-abi-order`, based on exact `f077fd4`, with PR #44 as its
dependency. The row PR head remains frozen.

The frozen candidate passed 235 elaborator tests, 260 tests across 13 affected
caller targets, and all 47 architecture tests. The four new private row-choice
tests are included in the elaborator total. Formatting, selected all-feature
Clippy with warnings denied, and changed Markdown lint, links and authority
checks passed. All four original CLI row probes return `() : Unit` under
compiler SHA-256
`2804af5e51759ce27cfde0e1af88f7147eacaf4f96cb0d84c567d7b7d0f030fb`.

Receipts are retained in
`.worktrees/semantics-alignment-context-20261017/row-unification`:
`focused-summary.json` records commands, timings and equal source/configuration
pins before/after; `baseline-row-choices.log` records three failed baseline
regressions; `baseline-source-equality.json` authenticates the corrected source
fixture against the recorded baseline compiler's `type.argument` refusal;
`candidate-cli-results.json` records the four successful CLI probes. Initial
failed sweeps and the independent budget measurement remain available for
review. These checks establish focused candidate evidence, not a fresh full
workspace gate. Exact model runtime remains unavailable.

The ABI-order regression first passes owner-before-offset source admission and
then fails the consistently reordered offset-before-owner declaration on the
unchanged reviewed implementation. Its candidate checks cover original
source/Core reconstruction, independent image facts and coordinate tampering,
both native output orders and terminal extraction cleanup. The reversed native
test uses a real reversed-signature wrapper that forwards to SQLite in SQLite's
actual argument order; the baseline reversed SQLite declaration is admission-only.
Receipts remain in
`.worktrees/semantics-alignment-context-20261017/foreign-output-order`.

The local ABI package passed 68 focused unit tests, 14 source caller/output
tests, five native tests and all 47 architecture tests. Its six statement hosts
ran both normal and injected invalid-tail executions across both ABI orders,
scalar refusal and private-data mutation. Formatting and strict all-target Ash
Clippy passed. The changed Markdown adds no lint finding; the 82 pre-existing
specification line-length findings remain. `focused-pre-fixture-depth-repair-summary.json`
and `repair-summary.json` retain the successful unchanged compiler checks and
fresh repaired-fixture/native evidence. Setup failures remain explicit evidence,
including the copied-offset assertion moved before a deep result branch to
preserve the parser's existing structural-depth limit.

Before ABI PR publication, the user prioritized
[issue #45](https://github.com/dikini/ash-lang/issues/45), native-library CLI inputs.
Preserve this unreviewed ABI package as a recoverable local checkpoint on
`codex/foreign-output-abi-order`; no ABI PR has been published. Next owner: the
developer handles the separate Main-based CLI PR, then resumes this exact ABI
checkpoint after that PR's focused evidence, independent review and publication.
The row head, Main and `ffi-base` remain unchanged. Retention and all acceptance
below remain pending.

Acceptance remains separate for each original scope:

- [ ] Row unification: regression, negative and resource evidence; independent
  review; verified retention.
- [ ] ABI-order outputs and connected documentation: focused and real-wrapper
  native evidence; independent review; verified retention.
- [ ] Diagnostic precedence and primitive wording: focused evidence;
  independent review; verified retention.
- [ ] Final combined verification and acceptance on the intended retaining ref.

## Verification

For row unification, test source-order permutations, the reported domain and
row forms, concrete/single-member controls, inferred coalescence in both operand
directions, later enclosing constraints, inconsistent rows, occurs/lacks
refusal, rollback and exact-budget fresh retries on a 256 KiB stack. Run the
affected elaborator/row/source callers and architecture tests, formatting and
strict focused Clippy. Check changed Markdown links, artifact structure and
authority manually.

For ABI-order outputs, preserve distinct owner/offset slots, exact input,
representation, status, ownership and lifetime checks. Test both orders through
source, independent Core/image validation and a real native wrapper. Verify
initially null output storage, an independent copied offset, child-before-parent
completion and terminal invalid-tail extraction with no ordinary fallback,
no C replay and exactly one unpublished-owner cleanup. Use the existing
input-derived native preparation/startup meters for the product-library image
fixture. Run affected owner contract/admission, Core, post-record and native
callers, formatting, strict focused Clippy, architecture and manual specification
checks. No production work coefficient or limit changes are part of this repair.

These PR checks are partial verification. The next fresh full workspace gate
belongs to the developer at the connected output/checking completion boundary,
on the final combined candidate before Main. The root orchestrator owns that
checkpoint assignment and independent review; no per-PR full gate is required.
Record exact source/configuration pins, commands, results, log paths and timings
in the PR handoff. Exact model runtime is unavailable; requested developer
settings are GPT-6.1-sol/MAX.

## Discoveries

The row matcher discards a candidate's rollback point after local argument
unification makes progress. A later row or ordinary type constraint can then
reject a branch even though another substitution satisfies the whole equation.
Filtering out an already matched right member would break valid inferred
coalescence. Search must also consider an unmatched right member when every
left member already has an exact match.

The ordered owner-argument transaction also retains its remaining slots for
backtracking. The determination-conflict fixture therefore costs 44 Type work
units instead of 38: two pair slots, four scalar copies, three entry slots and
two argument frames replace four owner-tag units and one single-pair entry.
Its exact/one-short Type and constraint assertions and complete rollback checks
remain required. The production work limit is unchanged.

An existing diagnostic fixture expected rejection of the same satisfiable row
equation before capture checking. It now verifies successful specialization and
owned-discard execution; an inconsistent expected row retains its original
binding-initializer diagnostic obligation. The specification, rather than that
old assertion, governs admission.

Output acquisition already retains its owner's ABI operand and the offset's
separate ABI operand. Passive preparation incorrectly orders those roles, while
signature admission, Core lineage and runtime reporting assume owner field one
and offset field two. Deriving report positions from the retained coordinates
implements the current ABI-order rule. The guard still records a readable
non-null owner before fallible offset extraction; output order supplies no new
ownership or native-call authority.

## Deviations

None. The first repair implements the current row rule without changing the
language specification. Later packages remain separate.
