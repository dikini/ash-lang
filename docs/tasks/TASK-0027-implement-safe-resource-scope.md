# TASK-0027: Implement Safe Resource Scope

- ID: `TASK-0027`
- Status: active
- Related: [CP-0017](../proposals/CP-0017-safe-non-foreign-resource-scope.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [execution plan](../plans/2026-09-06-safe-resource-scope.md)

> This task organizes authorized work; CP-0017 owns the semantic transition.

## Dependencies

Baseline: `387c4eff925d1d4fdbad08c3eb3c02028bb01035`, the locally integrated
capture/discard checkpoint. Its full gate passed 2,156 tests; integration
revalidation passed 1,153 tests. Recheck the baseline before product edits.
The user approved scope-owned release with reusable cell access on 2026-09-06.

## Work

Implement CP-0017 using one product writer at a time, test-first bounded
increments, semantic review followed by Rust/resource review, and final
documentation verification. Use high reasoning for compiler/runtime and
semantic/resource reviews, medium for mechanical documentation work; never
exceed high. Keep commits unsigned per the user's instruction. Use the local
`.worktree/safe-resource-scope` checkout and retain local integration only.

## Progress

- Read-only semantic and implementation-boundary audits completed.
- The user approved the concrete resource contract after those audits.
- Moved the clean integration checkout to the active feature worktree and
  created `codex/safe-resource-scope`; integration remains at the baseline.
- Fresh full baseline verification is running before product changes.
- Accepted proposal, task and implementation plan recorded.
- Independent contract review required explicit owner-relative checking of
  dependent request payloads sent to outer handler clauses. CP-0017 now records
  that rule and the copied-payload/live-outer controls; no temporary lending
  discipline is introduced.
- The reviewer confirmed that the revised contract closes the reported gap.
- Moving the worktree exposed stale executable paths in Cargo's retained
  package cache. Rebuilding that cache restored all 74 specification-example
  tests without changing source or tests; the full baseline gate is rerunning.

## Verification

Use the proposal's positive, negative, abstraction, repeated-acquisition,
tamper, transform, exact-boundary/retry, deep teardown and locality corpus.
Run focused gates after each increment and `cargo xtask verify` at closure.
Verify changed documentation, links and artifact authority manually.
Only close CP/task/plan after the full implementation and evidence are retained.

## Discoveries

Generic effect type applications currently erase the instantiation before
runtime request selection. A generic `E<T>` helper under `E<Int>` fails with
`runtime.invalid-control-state`; monomorphic and internally handled controls
pass. Returned requesting closures fail similarly. CP-0017 explicitly corrects
this prerequisite and the corresponding blanket type-erasure wording.

Source-generated type abstractions contain inert values, transparent type
operations or authenticated method adapters, but Effect Core previously
admitted arbitrary bodies. Delaying those
arbitrary bodies could delay effects. Step 1 therefore independently enforces
the actual lowered forms before retaining lexical abstractions. This preserves
source order and avoids a general runtime aggregate-specialization mechanism;
Pure Core and source generalization are unchanged.

Ordinary closure environments retain unused preceding bindings, while ordinary
heap cells persist into observation. Resource payload ownership must therefore
stay with the acquired scope; non-owning access handles must not extend it.
Capture analysis currently has callable targets and clause owners only. New
stored dependencies and resource-owner obligations must be inferred even when
resource-bearing code contains no discard.

## Deviations

No scope expansion is authorized. The original 16/100 milestone forecast is a
relative weight, not a spent-work ledger or a new numeric budget. Do not invent
work-unit totals or borrow hooks, cleanup, FFI or a general ownership system.
