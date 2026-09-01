# TASK-0020: Implement the Resume-Required Effect Kernel

- ID: `TASK-0020`
- Status: active
- Related:
  - [CP-0013](../proposals/CP-0013-resume-required-effect-kernel.md)
  - [DN-0026](../design/DN-0026-effect-ash-resource-first-milestones.md)
  - [DN-0027](../design/DN-0027-effect-ash-program-design.md)
  - [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md)
  - [AD-0004](../decisions/AD-0004-small-step-semantic-method.md)
  - [AD-0007](../decisions/AD-0007-typed-core-dialects.md)
  - [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)
  - [Execution plan](../plans/2026-09-01-resume-required-effect-kernel.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

CP-0013 is accepted after one independent high-reasoning semantic review and a
bounded correction pass. Current `main` remains the pure `d1e323d` predecessor.
The planning baseline `65b339c`, which adds only DN-0027 and DN-0028 to that
predecessor, passes `cargo xtask verify`.

Product work uses `.worktree/cp0013-effect-kernel` on
`feature/cp0013-effect-kernel`, rooted at verified `main` commit `d1e323d`. It
carries the design, proposal, acceptance, authorization, and refined execution
map without merging a planning branch. Planning authorization commit
`b29c238` is carried as product commit `ffb94a2`; planning refinement commit
`e5f7340` is carried as product commit `32e4b1c`. Those artifacts authorize a
prospective product transition; they do not make effects current Ash.

Stop and return to CP-0013 if implementation needs a source, row, inference,
handler, continuation, Core, dynamic-semantics, failure, or resource rule
absent from the accepted proposal. Do not resolve a semantic gap in Rust.

Do not add a disposable experiment, checked discard, abortive or first-class
handlers, result-type-changing handlers, escaping or multi-shot continuations,
resources, providers, hooks, cleanup, foreign calls, async execution, dynamic
loading, runtime effect registration, general qualified row constraints, or a
production resource-limit increase.

Do not merge or push the product branch, tag a checkpoint or Effects Ash
milestone, delete a branch, or remove a worktree without separate user
direction. The Effects Ash milestone requires independent final review before
any merge is considered.

## Work

Execute the linked plan to:

- add the shared `EffectRow` and computation-type boundary before effect
  syntax, including exact identity, lacks constraints, bounded union,
  substitution, equality, unification, generalization, and ambiguity;
- reserve and project effect declarations, computation rows, requests,
  handlers, clauses, and resume while retaining stable module-owned effect and
  operation identities through summaries and imports;
- extend bidirectional checking and rank-1 inference with latent rows, explicit
  requests, exhaustive lexical handlers, exact-instance discharge, forwarding,
  and structural exactly-once resume usage;
- add a separate production effect Core dialect, independent validation,
  transforms, and an empty linked-entry-row gate while leaving the pure
  operation family uninhabited;
- implement ordered deep handling, forwarding, capture, and one-shot resume in
  the explicit evaluator using first-order data rather than Rust closures;
- retain the positive, negative, tamper, transform, diagnostic, exact-resource,
  retry, and stack-safe evidence required by CP-0013; and
- update the normative specification only with the complete product transition,
  complete independent reviews and verification, then remove completed
  transition artifacts from the product branch.

The accepted forecast is 17 work units. Allocate one unit to authorization,
four to row and computation typing, three to syntax and identity, four to
source typing, three to Core and evaluation, and two to specification and
closure. Stop and re-scope at the proposal boundary rather than spending later
milestone capacity when that forecast is exhausted.

## Progress

- CP-0013 was proposed in unsigned commit `392f976`.
- Explicit acceptance is recorded in unsigned commit `41be641`.
- The proposal contains no experiment and no later effects-ash milestone work.
- The pure planning baseline passes the complete verifier.
- Product commit `32e4b1c` has no `src/`, `tests/`, or `spec/` delta from base
  `d1e323d`, and `cargo xtask verify` passes there.
- Product commits through `b763db6` add effect rows, declarations, source
  forms, resolution, and identity preservation.
- Product commits through `2c07e68` add source typing and structural resume
  validation.
- Product commit `57f0b0a` adds and independently validates Effect Core by
  reusing the generic Core substrate.
- The current runtime checkpoint reuses the explicit evaluator machine for
  ordered handling and one-shot resume. Its focused tests pass; it remains
  uncommitted pending final review and verification.
- The normative specification remains unchanged until the complete retained
  product transition.

## Verification

During implementation, use focused tests for each RED/GREEN cycle. Run
formatting, all-target checking, diff hygiene, and the checkpoint's named test
set before each product commit. Run the complete verifier only at the fresh
product baseline and final retained checkpoint.

The final gate is:

```text
cargo xtask verify
markdownlint-cli2 docs spec README.md AGENTS.md
git diff --check
git status --short
```

Manual verification checks changed links and formal notation, exact CP-0013
rule coverage, source/Core/runtime agreement, pure-dialect locality, empty
entry rows, effect and operation identity preservation, deterministic
diagnostic precedence, exact applicable resource formulas, atomic publication
and retry, stack-safe disposal, and absence of Rust closures as language
continuations.

## Discoveries

Idempotent open rows cannot soundly infer `{E | R}` from `{E} union { | R}`
unless `R` already lacks `E`. The accepted kernel therefore rejects that
unqualified synthesis and permits an expected row to supply the lacks fact.
It also rejects a union of two unrelated unsolved tails rather than adding a
qualified row-constraint language.

Handlers are lexical, exhaustive, and result-type preserving. Their resume
capability is a structural scope fact, not a source value. Intervening
nonmatching handlers belong to captured control and are absent while an outer
selected clause runs.

The pure Core dialect remains closed. Effect Core may share structural value
families and the accepted operation-family seam, but its validator and
evaluator entry are separate production boundaries.

Ash compiler and runtime compute are strictly limited. Reuse an existing
owner, validator, budget, traversal, and machine before adding another. A new
proportional carrier or pass requires evidence that the existing machinery
cannot satisfy the accepted rule. If a slice exceeds its forecast, stop and
simplify it rather than consuming capacity assigned to later milestones.

## Deviations

None.
