# TASK-0013: Require Top-Level Interface Method Functions

- ID: `TASK-0013`
- Status: active
- Related:
  [CP-0007: Top-Level Interface Method Functions](../proposals/CP-0007-top-level-interface-method-functions.md),
  [DN-0023: Interfaces and Implementations](../design/DN-0023-interfaces-and-implementations.md),
  [execution plan](../plans/2026-08-25-top-level-interface-method-functions.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

CP-0007 is accepted. The completed interface increment already retains
checker-owned interface facts, positive-pattern implementation equations,
explicit Core evidence, independent evidence validation, and exact resource
budgets.

Current `main` also contributes DN-0024. Integration must preserve the feature
branch's retained checkpoint identities while reconciling that note with
implemented Modular Ash.

## Work

- Integrate current `main` into `feature/modular-ash` without rewriting retained
  checkpoint commits.
- Correct DN-0024 and its index and trajectory entries for current Modular Ash.
- Change interface admission from an arrow-anywhere search to an outer
  `Function` check while preserving diagnostic precedence and reason identity.
- Update positive, negative, end-to-end, exact-budget, and stack-safety
  evidence.
- Update the specification and retained design evidence.
- Repeat independent review and root verification until no actionable finding
  remains.

## Progress

Unsigned merge `78c6da9` reconciles current `main`. Unsigned commit `364c736`
enforces the outer `Function` requirement and retains its positive, negative,
precedence, and end-to-end tests. Unsigned commit `18c04fd` rebaselines exact
resource boundaries and adds iterative `ResolvedModule` cleanup for rejected
interface types. Unsigned commit `089c54e` updates the specification and
retained evidence. Unsigned commit `5210beb` corrects checkpoint scope and
progress reporting. Branch-wide review, root verification, the corrective
product checkpoint report, and closure of the temporary proposal, task, and
execution plan remain.

## Verification

- Focused RED/GREEN interface and resource tests
- `cargo fmt --check`
- `cargo check --locked --all-targets`
- `cargo test --locked --all-targets`
- `cargo clippy --locked --all-targets -- -D warnings`
- `cargo xtask verify`
- `markdownlint --disable MD013 -- README.md spec docs`
- `git diff --check`
- Manual relative-link, authority-boundary, and current-`main` integration
  review

## Discoveries

The arrow-anywhere rule admitted interface declarations that no positive-pattern
implementation equation could check. The existing Core and evidence pipeline
needs only the stronger admission invariant, not a representation change.

## Deviations

None.
