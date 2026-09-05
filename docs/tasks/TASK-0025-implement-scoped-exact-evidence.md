# TASK-0025: Implement Scoped Exact Evidence

- ID: `TASK-0025`
- Status: active
- Related: [CP-0015](../proposals/CP-0015-scoped-exact-evidence.md),
  [execution plan](../plans/2026-09-05-scoped-exact-evidence.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

CP-0015 is accepted at `2f657d8` under the user's explicit request to implement
the bounded slice autonomously. The product baseline is verified integration
tip `90f517d`. The active branch is `codex/scoped-exact-evidence` in the ignored
`.worktree/scoped-exact-evidence` checkout. Main-checkout diagnostics and
migration-planning changes are unrelated and must remain untouched.

The original forecast is seven relative milestone units, not a token/time
budget. The user sets no new numerical work cap. Keep one product writer and
use independent read-only subagents: high for implementation and semantic or
resource risk, medium for mechanical mapping and documentation. High is the
ceiling. No generic evidence framework, new solver, or prototype is authorized.

## Work

1. Carry the smallest pure-relation direct/forwarding pair through syntax,
   resolution, selection, linked authentication, ordinary Core, and execution.
2. Complete CP-0015's selection, improvement, method, and closure interactions.
3. Close tamper, resource, small-stack, and predecessor coverage with independent
   semantic and Rust/resource reviews.
4. Update normative specification and executable examples, run the full gate,
   retain evidence, close transition artifacts, and reconcile the completed
   checkpoint with the local milestone integration branch under AD-0011.

This does not authorize a merge into `main`, push, or tag. Use unsigned commits.
Return semantic gaps to CP-0015; a scope expansion requires user direction.

## Progress

- Baseline `CARGO_INCREMENTAL=0 cargo xtask verify` passed on 2026-09-05:
  formatting, metadata, build, Clippy, 1,968 tests across 59 binaries, and
  rustdoc with warnings denied. The ignored baseline log is
  `target/scoped-evidence-baseline.log`.
- Independent high semantic and medium implementation-mapping reviews converged
  the accepted contract. They required explicit method resume barriers,
  complete admission precedence, and inert Core authentication facts.
- Product implementation has not started. The first pair must fail because
  sequential `with` is absent before production code changes.

## Verification

For each coherent change retain its failing witness, focused passing command,
diff check, and commit. At the full gate run:

```text
CARGO_INCREMENTAL=0 cargo xtask verify
markdownlint --disable MD013 -- docs spec README.md AGENTS.md
git diff --check
git status --short
```

Review relative links, formal notation, semantic authority, every CP evidence
obligation, source failure ownership, exact work formulas, atomic publication,
retry, iterative teardown, Core transforms, runtime erasure, and no source facts
in summaries/imports. Correct all Critical and Important review findings.

## Discoveries

Existing evidence slots and flat selection plans are reusable. Retaining an
optional lexical-chain head per pending occurrence and one parent link per
source preserves deferred inference without copying active-source vectors or
closing inference early. Independent linked validation must derive availability
from the actual ordered source tree, not trust that retained head.

Ordinary nonrecursive Core method bindings and binder scope can represent
lexical methods and captures. A distinct producer in existing authentication
facts does not require a new runtime scope node or evaluator frame.

## Deviations

None. The user's autonomous instruction delegates bounded design and execution
choices, not new language scope. The proposal records those decisions rather
than duplicating them in a separate design document.
