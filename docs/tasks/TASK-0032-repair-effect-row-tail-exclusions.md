# TASK-0032: Repair Effect Row Tail Exclusions

- ID: `TASK-0032`
- Status: active

This task implements the existing row formation, substitution and unification
rules in [static semantics](../../spec/static-semantics.md#computation-types-and-effect-rows).
It does not change language semantics.

## Dependencies

The user authorized this bounded defect repair against `diag-ash`
(`9231b21228c5ccacbbee0cc0da60b380e5d2dc59`). The canonical programs and baseline
verifier are in ash-doc's `lab/effect-row-tail-exclusion` directory.

## Work

1. Reproduce ash-doc's two canonical callbacks at `diag-ash` (`9231b21`).
2. Trace source formation, scheme instantiation and callback unification.
3. Add a rejecting regression and positive controls; repair the lost obligation.
4. Run focused effect tests and `cargo xtask verify`.

## Progress

The baseline reproduction and rejecting regression are verified. Source rows
now retain their written exclusions, including argument provenance and kind
checks. Instantiation shares exclusions between occurrences of one row binder.
Inference retains exclusions after solving a tail and rechecks them when type
arguments change. Tests cover rollback and exact versus insufficient work
budgets. Declaration checking and effect-Core type projection now share the
signature's exclusions. The existing locally handled relay passes through
execution, and a new parameterized handler test covers equation and explicit
function checking. The retained-obligation field uses the existing row owner
and is registered in the architecture inventory.

The repaired compiler runs the canonical pure callback with status 0, stdout
`43 : Int` and empty stderr. It rejects the excluded callback with status 1,
empty stdout and `effect.row-exclusion`. The user's follow-up for precise human
reporting is implemented: inference retains the exclusion cause, English and
Bulgarian messages explain it without internal type/effect IDs, and JSON retains
the requirement and expected-type spans. The canonical CLI runs and diagnostic
regression verify both formats. Implementation and verification are complete in
the isolated worktree; the user has authorized integration into local `main`.

## Verification

Run the supplied verifier on the clean exact baseline. On the repaired branch,
run `cargo test --lib row_`, the effect and resource-scope integration tests,
and `cargo xtask verify`. Check the two canonical programs directly without
changing ash-doc's observation verifier. The pure callback must still print
`43 : Int`; the excluded callback must fail with a source diagnostic.

Verified results:

- The unchanged baseline verifier passes at the exact `diag-ash` commit,
  confirming the incorrect acceptance before the repair.
- The rejecting callback regression failed before the repair and passes after it.
- All 27 effect-typing tests, 23 effect-diagnostic tests and 80 row-related unit
  tests pass. Controls cover pure callbacks, ordinary polymorphic relays,
  distinct parameterized instances, open forwarding and locally handled prefixes.
- `cargo xtask verify` passes formatting, metadata, build, Clippy, all workspace
  tests and rustdoc. This includes 1,294 library tests, the ownership inventory,
  exact-budget and rollback checks, and existing recursion/resource stress tests.
- Changed Markdown passes lint and relative-link checks. Review confirms the
  specification and runtime reporting are unchanged.

## Discoveries

The supplied verifier reproduces the incorrect `44 : Int` for the excluded
callback. Source-row construction retained an empty lacks list even beside a
written known member. Tracing confirms that instantiation and callback solving
consequently saw no exclusion. Repairing formation alone is insufficient:
occurrences share a binder contract, and a closed row solution can still depend
on unsolved type arguments in its members or exclusions.

## Deviations

None: this repairs the existing formation and substitution rules, not semantics.

Do not alter `diag-ash`, ash-doc's pin, lessons or canonical evidence.
