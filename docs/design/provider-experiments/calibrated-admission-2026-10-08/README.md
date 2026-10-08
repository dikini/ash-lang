# Calibrated public-driver admission, 2026-10-08

This is implementation evidence for the bounded
[DN-0036 experiment](../../DN-0036-foreign-library-and-memory-provider-experiments.md).
The user accepted the current completed cost measurements and authorized
calibrated admission with explicitly reported deficits of at most 10%.
It does not change current Ash semantics or establish production architecture.

## Selected allowance

The ordinary modular public driver now selects separate cumulative allowances
for source checking, final elaboration and independent Core validation. The
largest completed measurements are rounded up to 65,536 charged units. Each
rounded nominal budget gets at most another 10%, truncated to whole units.
The margin's denominator is the nominal budget; rounding headroom is separate.

| Phase | Completed measured maximum | Nominal budget | Hard stopping limit |
| --- | ---: | ---: | ---: |
| Source checking | 1,212,707 | 1,245,184 | 1,369,702 |
| Final elaborator | 376,641 | 393,216 | 432,537 |
| Independent Core | 1,609,087 | 1,638,400 | 1,802,240 |

The earlier completed Core measurement 1,609,101 also fits the same allowance.
The calibration input is pinned at
[`53780ef`](https://github.com/dikini/ash-lang/blob/53780efced5e3a569c22f9ddd3dfd296889f8612/docs/design/provider-experiments/resource-calibration/decision-budget-inputs.json).
Charged units include traversal, comparisons, records and reservations; they
are neither executed instructions nor a conversion from CPU time or RSS.
These bounds are a practical experimental admission policy for continued
feature development, not a universal complexity bound or an optimization.

Only the public modular driver selects the larger allowances. Standalone
Type work remains 327,680 and standalone Core work remains 983,040. Explicit
caller budgets retain their exact limits. Resolution, linked-interface
preparation, constraints, syntax, builders, rewrites, allocation admission,
runtime and depth limits retain their existing policy. In particular, earlier
linked-interface provider preparation has its own ledger; the final-elaborator
measurement covers applying its checked result, lowering and final zonking.

Checking, preparation and independent validation run once, with no retry after
exhaustion. Core helpers debit the selected validator's remaining allowance
and charge their actual child work back to the parent on failure as well as
success. Scope, kind, identity, evidence and native ownership checks remain
required.

## Explicit reporting

`Observation.compilation_work()` returns the source, final-elaborator and
independent-Core measurements. Each `PhaseCost` contains its owning phase,
charged `used` count and `completed` flag. Its `assessment()` method derives a
`WorkAssessment` variant without duplicating the charged count:

- `WithinBudget`;
- `AcceptedDeficit { units }`, an explicit future optimization target;
- `OutsideAllowance { units }`.

`phase.budget()` and `phase.hard_limit()` expose the denominators and stopping
limits. `optimization_target()` identifies accepted deficits. A successful
public run completes all three observed phases. A cost report grants no
checking or Core authority.

`FileFailure.compilation_work()` retains completed prior phases and measured
partial failing phases without replacing the original diagnostic. Absent
fields mean unobserved. A partial charged count does not estimate all work
needed to finish: the next refused bulk reservation may exceed the remaining
allowance even when the reported completed charges fit the nominal budget.
Input loading failures acquire no fabricated compiler measurements.

CPU/RSS assessment remains separate and offline. The
[adopted physical assessment](https://github.com/dikini/ash-lang/blob/ed3764a15f7f00e7059c3eb3eae1f6e74309040f/docs/design/provider-experiments/resource-calibration/accepted-deficits.md)
accepts measured excesses up to 10% against each original calibrated review
threshold and current-workload target. It records the baseline, observed
cost, absolute and relative deficit, and optimization target. A larger excess
requires review; missing or out-of-range measurements remain outside calibration.
Its 52 primary measured cases need no accepted deficit. The separately retained
structural cross-check has nine accepted and five outside-calibration cases;
nine IDs overlap the primary set. This is recalibration on examined data,
not unseen-program validation or a fresh CPU/RSS measurement of this change.

## Execution evidence and boundary

The four original expanded SQLite assertions pass through the public driver:
copying Unicode/bytes/nulls/empty values, rejected bound NUL, persistence with
statement reuse and reopening, and captured-control resume without reacquisition.
The complete connected batch passes 69 integration tests, including native
arena lifecycle, retention, rows, source control and reporting. The focused
18 driver tests pass, including independent Core failure propagation and
exact cumulative parent-prefix admission. The exact nominal/margin/first-refused
unit policy boundary passes separately. After the final report representation
refinement, all 40 focused tests pass again. Commands, pins and results are in
the [evidence index](evidence.md); the [contract review](review.md) records its
findings and resolution.

The larger SQLite library, native adapter and test inputs are preserved
independent work. They were used unchanged as regression inputs in Common;
this shared delivery does not silently commit them. Its input and executable
source hashes, commands and logs are recorded in the adjacent evidence index.
SQLite's preserving delivery and example-host reporting follow the verified
shared integration. Arena scalar allocation and proof/Core alignment retain
their separate scope and status.
