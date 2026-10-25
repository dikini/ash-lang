# Private checked owner boundary verification

This is partial TASK-0053 implementation evidence on retained PR101
`c51089c8b6de76384361283f671d1f2dbf3ad58e`, under
[the task](https://github.com/dikini/ash-lang/blob/2766e8260e2590d9ebdca7abd699115b3cd02a8a/docs/tasks/TASK-0053-checked-owner-core-execution.md). It does not change
Ash semantics or approve public execution.

The existing physical owner slot now retains the checked boundary journal.
Mandatory capacity is prepared before entry, returned ownership is recorded
before source publication, and native finish disposition/K precede fallible
source delivery. Required source continuation remains separate from consumption.
The authenticated supported sequence has two resource interpretations, two window
requests, and one distinct checked-copy primitive. Repeated non-finishing events
cannot consume its mandatory Finish cell or work reserve.

## Observed focused result

All eleven exact units passed, each selecting one test. The genuine eight-byte
fixture passed source/summary/link/independent-Core preparation before its five
journal events. Native returns and completion remain injected Rust unit data.
The real private `return_source_view_call` phase copied initialized safe Rust
storage `[5, 255, 0, 65, 66, 67, 0, 9]`, produced independent Bytes and recorded
its exact window/application/function coordinates. Key, Extent, H, donor-slot,
and short/spent-work controls performed no reads or successful observations.
An actual subsequent source-body failure retained the completed copy event and
terminal state. These tests grant no executable approval or protected context.

[Actual results](actual/readback.json), [command receipts](actual/batch-results.json)
and the [execution inventory](actual/execution-manifest.json) retain the outcome.
All 22 before/after maps, each covering 4,798 files, matched. The test executable
was observed as 854,348,032 bytes with SHA-256
`39adb6c4998debda2f7ca72d64f486dd86186d3d2f8fab18d9fb2e9a0dc08d77`.
It is not copied here. All owned command groups were empty after reaping, tool
pins matched, and these eleven logs contained no compiler warnings. Resource and
cache figures are samples, not hard quotas or complete peak proofs.

The [source pins](preparation/source-manifest.json),
[finite selectors](preparation/proposal.json) and [operator](preparation/verify-run.py)
are historical records with original host paths, not instructions to rerun an
unassigned command. These original receipts remain historical. Later mechanical lint corrections and
their fresh verification are recorded below; their results are not transferred
across source maps.

## Preserved failures and limits

The [first attempt](history/compile/phase-01.receipt.json) failed compilation with
three type errors and selected no tests. The
[next attempt](history/inventory/phase-01.receipt.json) compiled, then its first
test found the incorrect explicit-interpretation assertion `2 != 4`; its remaining
nine selectors did not run. That run also exposed four private-interface warnings.
The repair counts actual window mappings and narrows visibility. Neither failure
is credited as a semantic red. Two later intermediate source snapshots were
superseded before launch; the earlier e917 batch was cancelled before start.

The first affected batch passed 55 units, then Clippy refused three nested-if
lints. Its [receipt inventory](history/affected-lint/execution-manifest.json) is
separate from the next [test-lint attempt](history/test-lint/execution-manifest.json),
which found re-export placement, fixture type complexity and another nested-if.
Neither lint failure is a semantic test failure. The repairs only collapse
conditionals, name the existing tuple type and relocate unchanged re-exports.

## Final affected verification

The repaired source passed Clippy with warnings denied, all eleven connected
controls and 55 affected units: 66 distinct tests, with no duplicate selections.
The [unit readback](final/units/readback.json),
[original inventory](final/units/execution-manifest.json) and
[frozen source/fixture pins](final/preparation/manifest.json) preserve that scope.
All 50 before/after maps covered the same 4,868 files. The library test executable
was observed as 854,271,104 bytes, SHA-256
`8b5b4a0a455dec5d07987aa2f79969006fd18d773d87f08690be6e83a6e1bd4e`.

A separately authorized [legacy batch](final/legacy/readback.json) passed three
existing exact tests: static and shared scalar destruction captures, then byte
read/write and mutation refusal. Their unchanged helpers asserted exact results
and cleanup traces; successful stdout/trace is captured by the test harness.
Transient generated binaries were deleted by those helpers and are not copied
or assigned invented pins. The actual integration test executable was observed
as 590,909,984 bytes, SHA-256
`7cf9201ca5fe832c0a89c004f6d3914a4c6806d7338e7288e39a57f807141477`.
The [legacy inventory](final/legacy/execution-manifest.json) records actual tools,
commands, test artifacts, input equality and settled owned groups. These are
legacy regression results, not checked native or immutable-execution authority.

Both final batches used the same repaired source map and unchanged tool pins.
All commands exited zero, children were reaped and owned groups were empty.
Resource/cache observations remain sampled figures. Independent result audits
cleared both batches; final published-head review remains pending. The checked fixture C helper remains unbuilt/unexecuted.
There is no evidence here of checked C allocation, checked native Free, authored
checked Trace, deployed checked startup or the complete connected F-core path. Public build/binding/
initializer/report guards remain closed. Complete checked producer closure,
independent protected approval/context and immutable same-fd launch remain later
components. All broad F4/F6 acceptance criteria remain unchecked; unsupported
checked byte-read/write/NUL and dependency-owner paths are not silently enabled.

[Provenance and omissions](provenance.json) distinguish exact copied originals,
derived gzip containers and external records. Each raw log is retained once in
compressed form; one complete source map represents the equal maps, without
copying caches, binaries or full source archives. The
[bounded streaming verifier](verify_evidence.py) checks original hashes and decoded
content under finite limits. The [final receipt](final-verification.json) is archival verification, not runtime
authority; the original [early-payload receipt](verification.json) remains historical. External file availability is not promised.
