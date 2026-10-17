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
[PR #48](https://github.com/dikini/ash-lang/pull/48) has
[clear independent review](https://github.com/dikini/ash-lang/pull/48#pullrequestreview-5560259300)
at `0bd5f7b`. Unsigned merge `55f30714c2bb040f6651ac6898d433abbe2c1004` retains its
exact tree on `integration/semantics-alignment`; canonical source, configuration,
tool, environment, external-input and selected-artifact equality connects the
focused evidence to that result.
[Independent retained verification](https://github.com/dikini/ash-lang/pull/48#issuecomment-6241839571)
confirms that exact result.
[Issue #46 acceptance](https://github.com/dikini/ash-lang/issues/46#issuecomment-6241851985)
is closed with its original body preserved. The baseline documentation conflict
is resolved; the final combined gate and Main retention remain pending.
The original receipts and explicit setup failures remain in
`.worktrees/semantics-alignment-context-20261017/foreign-output-order`.

Issue #46's overview, detailed-rule and tool-guide alignment is retained
through PR #48. At `ffi-base`, the detailed rules and implementation already
admitted bounded sealed copy windows in permitted direct provider phases. The
corrected overview and tool guide describe that existing scope; this adds no
capability or tag rewrite. The privileged lifecycle-wrapper exclusion remains.
Current composition receipts
belong in
`.worktrees/semantics-alignment-context-20261017/foreign-output-refresh-on-b8`.

The final package starts from retained integration `55f3071` on
`codex/diagnostic-precedence-alignment`. The affected kind and resolver sources
and representation-cycle pass still equal `ffi-base`. The corrected baseline
regressions pass two controls and fail seven precedence/source-classification
cases. An earlier global and a representation can both report
`kind.expected-type`; their winning primary and related spans and structured
kinds distinguish the failures. The repair checks module representations, then
representation cycles, then remaining kinds without changing the existing
cycle algorithm or its closing/member labels. Primitive contextual wording
now describes the operand heap threaded by the existing machine; it changes
no runtime rule.

Diagnostic-contract decision: an arity-invalid effect instance in a written
type reports `effect.argument-count` with expected/supplied counts, its complete
application and the original effect header. This implements existing arity-before-kind
source responsibility under AD-0006. Admission-only scalar origins preserve
those sites through row canonicalization and are discarded before resolved
module publication. Imported and authenticated/body-free carrier corruption
retains `KindInternalCause::EffectArgumentCount`; there is no blanket remapping.
The candidate passes 889 focused cases: 403 kind/resolver/elaborator units,
11 new precedence regressions, 252 front-end/module callers, 161 diagnostic
callers, 47 architecture cases, 12 source-owner controls, the both-order image
control, the real reversed-output SQLite host and the mixed static/shared CLI
fixture. All 14 focused commands pass, including formatting and strict
all-target/all-feature Clippy. Canonical inputs and state agree before/after.
Changed Markdown has the same 80 existing line-length findings, no new finding
and no broken relative link. The subsequent results prose has separate metadata
and manual-check evidence. Independent review, retention and the final combined
gate remain pending for this package. Receipts belong in
`.worktrees/semantics-alignment-context-20261017/diagnostic-precedence`.

Acceptance remains separate for each original scope:

- [x] Row unification: regression, negative and resource evidence; independent
  review; verified retention.
- [x] ABI-order outputs and connected documentation: focused and real-wrapper
  native evidence; independent review; verified retention.
- [ ] Diagnostic precedence and primitive wording: focused evidence;
  independent review; verified retention.
- [ ] Final combined verification and acceptance on the intended retaining ref.

Delivered: the row repair, current focused/native evidence and independent
review are retained on `integration/semantics-alignment` at `b8fe5b3` through
PR #44. ABI-order outputs and the connected issue #46 documentation correction
are retained at `55f3071` through PR #48, with
[retained-result evidence](https://github.com/dikini/ash-lang/pull/48#issuecomment-6241785767).
Exact records are
`.worktrees/semantics-alignment-context-20261017/row-refresh-on-main1573/integration/retained-handoff.json`
and
`.worktrees/semantics-alignment-context-20261017/foreign-output-refresh-on-b8/integration/retained-handoff.json`.

Remaining: diagnostic precedence, primitive wording, the final combined fresh
workspace gate and verified Main retention. These original combined obligations
remain unchecked above.
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

For diagnostic precedence, test representation kinds before interface arity,
determination, earlier global and local kinds; representation cycles before
remaining kinds and interface checks; and remaining effect kinds before
determination and method kinds. Assert causal spans and structured facts when
reason codes coincide, preserve cycle-closing/member labels and retain repaired
positive and later-failure controls. Test nested written effect arity locally
and through imported headers, type and row arguments, zero arguments, structured
counts, both catalogues, and retained/internal negative controls. Keep exact
origin/label work boundaries, fresh retries and small-stack graph checks. Run
affected kind, resolution, elaboration, module, diagnostic, row and native/image
composition callers, architecture, formatting, strict Clippy and manual docs.

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

The separate representation stage charges one scan cell per declaration.
The relational-interface fixture therefore costs 11 rather than 10 work cells;
the two-nominal partition fixture costs 12 rather than 10. Their one-short,
exact and fresh-retry assertions remain. A malformed written effect origin costs
one header lookup and one retained scalar record; source diagnostic lookup and
its related label each cost one work cell. Production limits are unchanged.

## Deviations

None. The row, output and checking repairs implement current rules. The
connected acquisition, copy-window and primitive-heap wording corrections add
no semantic mechanism. The diagnostic package remains a separate delivery.
