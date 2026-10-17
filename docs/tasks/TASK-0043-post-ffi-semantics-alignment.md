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
Candidate review, publication and retained verification remain pending.

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

## Deviations

None. The first repair implements the current row rule without changing the
language specification. Later packages remain separate.
