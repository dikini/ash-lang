# SQLite copying delivery evidence, 2026-10-08

This records a checked source checkpoint under
[DN-0036](../../DN-0036-foreign-library-and-memory-provider-experiments.md).
It establishes experimental execution evidence, not current Ash semantics or
production architecture. Final preserving integration and the combined
whole-workspace gate are recorded separately in
[execution](../execution.md#current-sqlite-checkpoint).

## Source and admission

SQLite imports corrected Original `cce01be` through unsigned merge `817f3828`.
[Source pins](source-pins.json) authenticate the executable graph, native
adapter, configuration, public fixtures, host and packaged programs. The
seven of eight packaged Ash files match their public fixtures exactly;
the eighth, `session-entry.ash`, substitutes `session.sqlite3` at both path
literals and runs from an exclusively owned temporary directory.

The [public driver policy](../calibrated-admission-2026-10-08/README.md) admits
separately measured source, final-elaborator and independent-Core work under
calibrated budgets. No diagnostic feature, temporary ceiling or retry is used.
All fifteen measured phases complete within their nominal budgets, with no
accepted deficit. Copying still charges 1,212,707 source units: this delivery
does not claim reduced algorithmic work. Charged units are neither CPU time nor
peak memory. Validation and standalone/explicit budgets remain unchanged.

## Fresh checks

[Check results](checks.json) record serial commands, returns and elapsed times.
Cargo uses one job and an empty `RUSTC_WRAPPER`. Formatting, the final host
build, affected adapter all-target Clippy and all three public SQLite
test-target Clippy pass; lints use warnings denied. Adjacent logs retain their
actual outputs.

[Host results](host-results.json) and the five `*.ash.stdout` files record actual
execution of Unicode TEXT, full copying, transaction/reuse/reopen persistence,
capture/resume and owned discard through `sqlite_session`. Every full source
value, native completion count, copied input/output size and zero retained-owner
count matches the existing public assertions. Finish dispatch precedes native
completion; dependent finalization precedes close. The first session close
precedes reopening the real database. Discard's diagnostic queries run before
finalization. Fault injection and `close_v2` are absent.

The exact supplementary forwarding regression passes with one native integer
read, `Completed(Completed(Ok(42), Closed), Closed)` and actual source completion
([log](forwarding.log)). Its fixture is the preserved calibration input. The
original copying test file remains an exact byte prefix; this case supplements
the original acceptance programs.

An actual typing-error entry returns a failing exit, preserves its original
error, reports partial source work with `completed=false` and marks later
phases unobserved ([receipt](failure-report.json)). The host never substitutes
zero for absent measurements. The archived `verify_examples.py` records the
local verification runner; portable author reproduction is in the
[example package](../examples/sqlite-copying/README.md).

## Reused evidence and limits

Common's [final tests](../calibrated-admission-2026-10-08/final-tests.json) pass all
seventeen original copying/session/control cases with their complete values,
native lifecycle and copy assertions. SQLite reuses those passes rather than
rerunning unchanged cases for an import. Executable source inputs match the
Common pin manifest. The documented differences are opening test comments, a
later test-only Clippy inequality correction and the appended forwarding case.
The shared harness's existing unused-code annotation matches Common exactly.

Independent read-only reviews find no actionable native/library, host-reporting
or selected-contract issues. The contract reconciliation preserves NOMEM as
`NativeFailure`, reserved `AllocationFailure`, terminal host refusal, stable
prior coordinates and exact manifest authentication. It does not promote the
experiment into `spec/`.

The earlier sixty-case native adapter run remains historical; it was not
repeated for the reporter change. This checkpoint does not claim a fresh full
adapter execution run or a completed integrated `cargo xtask verify`. The
coordinator retains the final combined gate, preserving merge and any later
main-retention decision.
