# TASK-0043: Post-ffi semantics alignment

- ID: `TASK-0043`
- Status: active
- Related: [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [issue #46](https://github.com/dikini/ash-lang/issues/46),
  [current static semantics](../../spec/static-semantics.md),
  [current dynamic semantics](../../spec/dynamic-semantics.md)

> This task organizes authorized repairs. It does not define Ash semantics.

## Dependencies

The user authorized row-unification repair first, then reconciliation of the
remaining specification/implementation mismatches, with focused regressions,
independent review and separate PRs. The original baseline and immutable
`ffi-base` remain `354c76b`; the completed ffi milestone remains complete. The
user subsequently prioritized issue #45, now retained on Main `1573ae8`. Refresh
the semantics stack onto `integration/semantics-alignment` from that Main. The
user authorizes autonomous unsigned commits and merges through PRs. PM assigns
verification, independent review and integration; no new human approval is needed.

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

The original row delivery used `codex/row-unification-backtracking` from `354c76b`.
Baseline source probes are retained at
`.worktrees/semantics-alignment-context-20261017/baseline-review`; they identify
the failing generic row, passing concrete/single-member controls and compiler
SHA-256 `8621279869c3c87f297c80406a0bad182651eb382fccec35be60a244d4ea0ebb`.
[PR #44](https://github.com/dikini/ash-lang/pull/44) originally published the row
repair at `f077fd4`, with
[clear independent review](https://github.com/dikini/ash-lang/pull/44#pullrequestreview-5559465031).
The refresh at `c64f321` has
[clear current re-review](https://github.com/dikini/ash-lang/pull/44#pullrequestreview-5560128656).
Unsigned merge `b8fe5b32886cd0869a63e1e196218f5643118bc1` retains that exact tree
on `integration/semantics-alignment`, preserving the original row implementation
and test bytes.
[Independent retained verification](https://github.com/dikini/ash-lang/pull/44#issuecomment-6241329442)
confirms that result. Canonical source, configuration, tool, environment, external-input
and selected artifact equality connects the current focused evidence to that
retained result. Main remains `1573ae8`; its elaborator still equals the original
failing baseline. The final combined gate and Main row retention remain pending.

The refreshed composition passes 235 elaborator tests, 260 cases across the 13
affected caller targets, 47 architecture tests, three concurrent native-image
controls and the real mixed static/shared CLI fixture. All four retained CLI row
probes return `() : Unit`. Formatting, strict all-target/all-feature Clippy and
changed Markdown checks pass. Canonical source/configuration/tool/environment
pins agree before and after those focused checks. The subsequent task-results
prose has separate metadata/manual-check evidence. These results support bounded
row retention; the final combined gate and Main retention remain pending.

The original frozen candidate passed 235 elaborator tests, 260 tests across 13
affected caller targets, and all 47 architecture tests. The four new private row-choice
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

The refresh also carries TASK-0044 completion and active-index cleanup. Its CLI
code is already retained on Main `1573ae8`, and
[issue #45 acceptance is closed](https://github.com/dikini/ash-lang/issues/45#issuecomment-6240835155).
That task completion record and active-index cleanup are now retained on the
integration branch through PR #44. Their final Main retention follows the combined
semantics integration. The last fresh seven-stage gate is the issue #45 gate at
Main `1573ae8`; it establishes no fresh workspace gate for the added row repair.
Current refresh and retained receipts belong in
`.worktrees/semantics-alignment-context-20261017/row-refresh-on-main1573`.

The local ABI checkpoint `f52fac2` preserves the package paused for issue #45.
It is now composed with integration `b8fe5b3` on
`codex/foreign-output-abi-order`. The source regression passed owner-before-offset
admission and rejected a consistently reordered offset-before-owner declaration
before implementation. The saved package passed 68 focused unit tests, 14 source
caller/output tests, five native tests and all 47 architecture tests. Its six
statement hosts exercised both ABI orders, normal and invalid-tail returns,
scalar refusal and private-data mutation.
The refreshed composition passes those 68 affected unit tests, four row-choice
controls, 14 source caller/output tests, five native tests and 47 architecture
checks. The six current native hosts retain all twelve normal/injected
executions across both output orders. Formatting and strict all-target/all-feature
Clippy pass. Source, configuration, tool, environment and explicit external-input
pins agree before and after all 14 focused commands. Changed Markdown has no new
finding or broken link; the same 84 existing line-length findings remain.
Independent review and verified retention of this package remain pending.
The original receipts and explicit setup failures remain in
`.worktrees/semantics-alignment-context-20261017/foreign-output-order`.

This delivery prioritizes issue #46's overview, detailed-rule and tool-guide
alignment. At `ffi-base`, the detailed rules and implementation already admitted
bounded sealed copy windows in permitted direct provider phases. The overview
and tool guide need correction; this adds no capability or tag rewrite. The
privileged lifecycle-wrapper exclusion remains. Current composition receipts
belong in
`.worktrees/semantics-alignment-context-20261017/foreign-output-refresh-on-b8`.

Acceptance remains separate for each original scope:

- [x] Row unification: regression, negative and resource evidence; independent
  review; verified retention.
- [ ] ABI-order outputs and connected documentation: focused and real-wrapper
  native evidence; independent review; verified retention.
- [ ] Diagnostic precedence and primitive wording: focused evidence;
  independent review; verified retention.
- [ ] Final combined verification and acceptance on the intended retaining ref.

Delivered: the row repair, current focused/native evidence and independent
review are retained on `integration/semantics-alignment` at `b8fe5b3` through
PR #44. The record is
`.worktrees/semantics-alignment-context-20261017/row-refresh-on-main1573/integration/retained-handoff.json`.

Remaining: ABI/output repair and issue #46 documentation, diagnostic precedence,
primitive wording, the final combined fresh workspace gate and verified Main
retention. These original combined obligations remain unchecked above.
Owner: the developer under PM's checkpoint and review assignment.

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
on the final combined candidate before Main, after ABI and diagnostic deliveries.
PM owns that checkpoint assignment and independent review; no per-PR semantic
full gate is required.
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
ownership or native-call authority. Reversed native execution uses a dedicated
reversed-signature wrapper that forwards to SQLite in its actual argument order;
the reversed declaration naming SQLite directly remains admission-only.

## Deviations

None. The row and output repairs implement current rules. The connected
acquisition and copy-window wording corrections add no semantic mechanism.
The diagnostic package remains separate.
