# TASK-0033: Repair Opaque Newtype Imports

- ID: `TASK-0033`
- Status: active

This user-authorized repair implements the existing
[import closure](../../spec/name-resolution.md#imports-and-namespaces) and
[opaque declaration](../../spec/name-resolution.md#public-private-and-opaque-declarations)
rules. It does not change language semantics.

## Dependencies

Start from `diag-ash`, `40c964c69c007ba81ec6bdbac34e31ad24fec9c7`.
The ash-doc `functions-libraries` worktree supplies the canonical reproduction
in `lab/opaque-newtype-import` and the unchanged L2 lesson files.

## Work

Reproduce the baseline, add upstream regressions before product changes, and
repair the inconsistency between named and scheme-retained nominal metadata.
Preserve source opacity and authentication of canonical representations.

## Progress

The exact baseline verifier reproduced the failures and passing controls.
Before product changes, the two new integration regressions failed with
`resolve.internal-state`; the 19 existing module-newtype tests passed.

The repair compares canonical representations and provenance across named,
scheme, duplicate-function and constructor-payload routes. Opaque source facts
still withhold representations and constructors. Hidden-to-opaque promotion
retains canonical metadata before removing the hidden inline representation.
All fallible preparation precedes that promotion.

Implementation and focused verification are complete. Integration into `main`
and publication remain outside this task's authorization.

## Verification

Cover both targeted orders, facade routes, unused and called imported functions,
ordinary opaque data, transparent newtypes, and source-owned rejection of opaque
constructors. Check canonical metadata conflict and resource-budget invariants.
The 21 module-newtype tests pass, including complete imports, both targeted
orders, separate and combined facades, duplicate function routes, and transparent
constructor payloads containing opaque newtypes. The focused resolver test
checks exact and one-short type/constraint budgets, retry without partial
promotion, and rejection of conflicting representations and provenance.

All four unchanged lab clients now return `42 : Int` with status 0 and empty
stderr. Unchanged L2 `06-opaque-client.ash` does the same.
`07-hidden-constructor.ash` returns status 1 and source-owned
`resolve.opaque-constructor` JSON. Human output explains the inaccessible
constructor and labels both its use and declaration. Both renderers are covered
by the upstream constructor regression; no diagnostic catalog change is needed.

`cargo xtask verify` passes, including formatting, build, Clippy, all tests and
rustdoc. The final expanded integration matrix and all-target Clippy also pass.
Review found no correctness or opacity defect; its two requested route cases
are included in the passing matrix. Changed documentation links and authority
boundaries were checked manually.

## Discoveries

The named route withholds the representation and retains canonical linkage
metadata separately. The scheme route instead places the canonical
representation in its hidden nominal projection. Strict metadata merging then
compares incompatible projections of the same defining fact.

## Deviations

None. Leave `diag-ash`, ash-doc's pin and lesson state unchanged. Supply an exact
fixed commit without assuming authorization to merge or push it.
