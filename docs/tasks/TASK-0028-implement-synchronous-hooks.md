# TASK-0028: Implement Synchronous Hooks

- ID: `TASK-0028`
- Status: active
- Related: [CP-0018](../proposals/CP-0018-synchronous-typed-hooks.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [execution plan](../plans/2026-09-07-synchronous-hooks.md)

> This task organizes authorized implementation. CP-0018 owns the semantic
> transition; neither this task nor its plan defines language behavior.

## Dependencies

The user accepted CP-0018 and subsequently authorized its implementation with
subagents, with reasoning capped at high. The starting integration tip is
`ec8f86165689306a5301732a2ec995f8f7487686`, retaining the verified safe-resource
checkpoint and accepted hook proposal. `main` remains separate.

## Work

Implement the whole CP-0018 contract: typed named transformation hooks, empty
roots, scoped registration, forwarding-first order, visible callback effects,
registration-site handler placement, nested-chain visibility, dependency and
completion checking, authenticated Core, and bounded runtime ownership.
Retain every HOOK-01 through HOOK-10 evidence obligation, including generic
instance coincidence and provably absent target rows.

Use `.worktree/synchronous-hooks` on `codex/synchronous-hooks`, with one product
writer at a time. Implementers and semantic/Rust-resource reviewers use high
reasoning; mechanical documentation checks use medium. The parent owns task,
plan, proposal, specification, staging and unsigned commits. Review is read-only.
Do not push, tag, merge `main`, or change signing configuration.

## Progress

- Confirmed the accepted proposal and implementation authorization.
- Moved the clean integration checkout to the product worktree and created its
  feature branch; the integration ref remains at the starting tip.
- Refreshed only disposable Ash/xtask build artifacts after moving the checkout,
  so path-dependent test binaries do not retain the preceding checkout path.
- Fresh `CARGO_INCREMENTAL=0 cargo xtask verify` baseline passed before product
  edits, including 1,099 library tests, all integration suites and rustdoc.
- The read-only high-reasoning implementation map and parent-owned execution
  plan are complete. The medium documentation audit passes after linking the
  lifecycle decision.
- Step 1 syntax and projection passed independent high-reasoning semantic and
  Rust/resource review. The parent repeated the focused tests (1,101 library,
  seven hook syntax and 93 predecessor tests), formatting, strict Clippy and
  narrow architecture inventory check successfully. Both forms still reject
  at resolution at that checkpoint.
- Step 2 began with real-driver identity-publication and unused-root witnesses.
  Both reached the expected temporary resolution rejection before product
  changes. Root implementation is undergoing final checks; registration remains
  unavailable.
- The implementer's combined hook/effect/resource integration gate passes:
  open-lacks admission and ambiguity rejection, imported helper transforms,
  phantom target retention, generic resource/control cases, kind precedence,
  source spans and the fresh-child 24-root/256-KiB direct pipeline. The corrected
  five-field architecture inventory passes its focused check.
- The parent pre-review-correction repeat passed 1,109 library tests, all 32
  architecture tests and 175 focused integration tests. Semantic review found
  row-error precedence and pattern-origin authentication gaps; the implementer
  also found a root-only partial-clone disposal issue. Both semantic regressions
  reproduced their failures before correction. All three fixes are applied and
  semantic re-review passes. The implementer's post-fix gate passes 1,110 library
  and 176 focused tests plus strict Clippy, inventory, formatting and diff checks.
  The parent repeated that gate successfully, including all 32 architecture
  tests. Rust/resource review found one remaining partial-clone failure path
  when an ordinary handler recomputes rows through a nested hook root. Its
  root-only correction passes Rust/resource re-review. The unchanged regression
  first overflowed during partial-clone disposal, then passed rollback,
  one-short exhaustion and two exact-budget retries in a fresh 256 KiB child.
  The final parent repeat passed 1,111 library and 176 focused integration tests,
  formatting, strict Clippy, Markdown lint and diff checks. Step 2 is retained
  in unsigned checkpoint `e801edb`; the final actual-field inventory also passed.
  Registration remains unavailable.
- A fresh high-reasoning implementer is reconstructing Step 3's registration
  structure and completion-proof boundaries before its first failing witnesses.

## Verification

Use CP-0018's complete named matrix: positive behavior, negative admission,
module/factory/evidence transport, same-site activations, transformed Core,
exact/one-short/retry budgets, capacity reuse, deep disposal and Pure locality.
Every product increment starts with a failing witness, preserves it unchanged
through correction, and closes semantic then Rust/resource review.

Run focused gates after each increment and `CARGO_INCREMENTAL=0 cargo xtask
verify` at closure. Verify all eight proposal-named specification/tool areas,
exact executable examples, Markdown lint, local links, formal notation and
artifact authority. Retain the complete verified product checkpoint before
removing CP/task/plan and their index entries. Follow
[AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md) for the unsigned
local merge, merged-checkout verification and clean feature-worktree removal.
Preserve unrelated main-checkout changes and all remote refs/tags.

## Discoveries

Resolved effect occurrences discarded argument type provenance. Hook-target
kind checking needs that original source information: the body-free kind API
deliberately reports malformed types as internal failures. Retain provenance on
the existing resolved occurrence, with charged ownership, and scope the new
kind check to hook targets. Registration can reuse the same source carrier.

The 24-root pipeline on a 256 KiB stack follows the existing resource-scope
control. Phase isolation found root resolution recursion first; explicit root
body scheduling removed that overflow. Module checking then exposed new-root
recursion in elaboration. Explicit body scheduling and direct construction of
the known typed identity clause remove that recursion; independent Core still
checks the clause relationships. Standalone load/resolve/check now succeeds at
that depth and stack size. The remaining `run_path` wrapper overflow also occurs
with 24 resource cells. The final fresh-child witness therefore follows the
predecessor's direct load/resolve/check/link/validate/evaluate/dispose helper,
without that wrapper. Ordinary handler behavior and the original
24-scope/256-KiB bounds are unchanged; this does not claim small-stack support
for the full driver wrapper.

The open-row root witness exposed a pre-existing Core subset comparison issue:
written known row members imply tail lacks facts, but the comparison treated
implicit and explicitly retained facts differently. A focused non-hook
regression now covers the charged normalization correction, unrelated lacks
rejection, exact work, one-short exhaustion and fresh retries. Root rows remain
least rows; the correction adds no new lacks assumption.
The same witness then reached a separate Core row-reconstruction failure:
source checking uses a lacks fact from the enclosing function annotation, while
the Core parameter type retains the unqualified tail. Reconstruction of that
existing lexical authority now uses the row variable's existing abstraction
owner and its independently checked `Forall` contract. Current row formation
already makes written members absent from that lexical tail. The correction
stays in charged Effect validation and preserves exact known members and
tail identity; descendant computed rows cannot justify their own added facts.
The helper witness passes through imports and both transforms; it has not been
replaced by an easier row case.

The surface tree has no separate iterative ownership API. Step 1 reuses the
existing iterative CST/projection paths and checks accepted surface disposal on
a small stack. Registration initializers can nest before a block, so each
registration charges one structural unit in addition to its body block.

The proposal review established that ordinary checking-only effect weakening
does not change Core's least body row. The new scopes must independently retain
their provably-absent target rule without dummy requests, body thunks, or relaxed
ordinary handler admission. Absence before generic instantiation is not grounds
for erasing a root or registration: later arguments can make instances equal.

## Deviations

None. Return any semantic contradiction to CP-0018 rather than replacing a
required case with blanket rejection or a different dispatch model. The original
nine-unit forecast is a relative milestone weight, not measured expenditure.
General cleanup, numeric priorities, manual deregistration, async hooks, foreign
providers and general ownership mechanisms remain excluded.
