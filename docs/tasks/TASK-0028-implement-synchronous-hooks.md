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

- The accepted proposal and implementation authorization are recorded. The
  feature worktree is `.worktree/synchronous-hooks`; the integration ref remains
  at `ec8f86165689306a5301732a2ec995f8f7487686`. Main's unrelated changes remain
  untouched.
- Fresh `CARGO_INCREMENTAL=0 cargo xtask verify` baseline passed before product
  edits, including 1,099 library tests, integration suites and rustdoc.
- Step 1 syntax and projection are retained in unsigned checkpoint `bb618e8`.
  Step 2 authenticated executable roots are retained in unsigned checkpoint
  `e801edb`. Both passed independent semantic and Rust/resource reviews.
- Step 3 registration structure and completion proof are retained in unsigned
  checkpoint `07bb726e`. Lowering
  retains a preceding callback binding, a non-interpreting completion owner and
  the ordinary generated forward–callback–resume clause. Independent linked
  Core proof rejects altered owner relationships, unsafe callback completion
  and callback-added escaping dependencies, including through both transforms.
- Anonymous callbacks check against their payload type while preserving latent
  effects and ordinary binding generalization. Owning tests cover exact work,
  every insufficient elaboration allowance, fresh retries, deep partial-state
  disposal and the 24-registration/256-KiB direct pipeline. The discoveries
  below distinguish harness alignment from later unchanged-witness corrections.
- Final independent semantic and Rust/resource reviews pass. The parent repeated
  1,131 library tests, 229 focused integration tests and all 32 architecture
  checks successfully on the corrected snapshot, plus formatting and full
  strict Clippy. The evidence-document audit passes. The six added inventory
  fields retain existing classifications; no check or limit is weakened.
- At the retained Step 3 checkpoint, both public Effect validators reject
  executable registration after completing proof, without a pure or unused
  callback exemption. That checkpoint is not registration runtime support.
- Steps 4 and 5 are implemented and verified. Registration uses a private
  owning frame and ordinary forward–callback–resume execution. Final high
  semantic and Rust/resource reviews pass, including the corrected duplicate
  handler and consumed-clause checks. Generic coincidence, tuple/projection
  dependencies and imported callback rows pass through both transforms.
- All eight specification/tool updates pass medium review, local-link and
  formal-notation checks, Markdown lint and the exact CLI test. The final
  parent `CARGO_INCREMENTAL=0 cargo xtask verify` completed all phases
  successfully on September 8, including 1,142 library tests, all 32
  architecture checks and 76 documentation-example tests. Its original tool
  session receipt was lost during context truncation; the completed log and
  terminated process were inspected. Merged-checkout verification will retain
  a separate process exit receipt.
- The complete product checkpoint, transition cleanup and unsigned local
  integration are next. No push, tag or main merge has occurred.

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

The generated callback binding generalized an anonymous identity function
before registration checking could supply its payload type. Reading that
binding's rigid monotype then rejected the valid callback. Independent review
identified this path, and the unchanged identity-lambda witness confirms it.
Correction must retain ordinary user-binding generalization and inferred latent
effects; a pure-only callback annotation would change the accepted contract.
The contextual correction uses the existing inferred-effect function check.
The registration task remains a borrowed scheduling detail. Frame measurements
ruled out enum growth and showed 176 bytes less caller stack in the registration
test. A hook-completion helper reduced the main frame but increased total live
stack and was removed. Extracting ordinary binding scheduling verbatim instead
reduces the shared frame from 109,152 to 106,944 bytes; that helper is absent from
the failing path. Both unchanged 24-scope/256-KiB witnesses pass afterward.

A same-typed callback substitution in actual linked Core exposed a completion
proof gap. Contextual value analysis seeded callable bodies but did not demand
the enclosing linked bindings, so calls could have no discovered target and
skip the unsafe callback. Demanding each actual control root's value port in
its existing context initializes those bindings through the existing analysis.
The unchanged substituted callback now rejects unsafe discard before the
temporary runtime gate, on base Core and both transforms. The honest callback
passes the full internal proof. An independent read-only trace confirms this
cause and correction; final Step 3 semantic and Rust/resource reviews pass.

Registration metadata enlarged shared expression and handler frames. Extracting
callback typing alone did not restore the root stack test. Boxing the new
optional contract moved the observed failure past resolution but did not close
the test. Separating direct typed registration lowering and its retained
metadata from ordinary handler emission restores the unchanged root stack test.
Existing root checks and ordinary emission remain intact. The deep registration
witness still overflowed beneath the shared handler frame. Direct registration
completion dispatch removes that frame; debugger traces then get through all
registration lowering and fail at the outer root. The unchanged direct root
test passes, while the matched root-only helper control fails. The registration
test is therefore aligned with the direct predecessor harness, retaining
the same 24 registrations, outer root, 256 KiB stack, compiler phases and
disposal on that thread, and passes. This harness change is separate from the
product corrections. An owner-erasure witness also exposed acceptance of a
registration-marked handler after its owner node was removed. The corrected
check includes surviving handler contracts as well as owner nodes; its
regression now passes.

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
