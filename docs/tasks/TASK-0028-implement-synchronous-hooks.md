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
  at resolution; executable roots are next.

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
