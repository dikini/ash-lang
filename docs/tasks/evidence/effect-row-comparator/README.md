# Effect-row comparator correctness (#114)

This delivery implements the existing unordered, idempotent effect-row rule.
The previous comparator could form a cycle between pure functions, explicit
empty-effectful functions and nonempty-effectful functions. It now compares the
existing semantic function view consistently by domain, result and latent row,
using the paid iterative work queue. It introduces no semantic proposal, cache,
Core admission limit or runtime authority change.

The test-only baseline on retained `a2f1c938` genuinely failed the first
idempotence assertion after its raw-representation and pure/empty equality/hash
prerequisites passed. Later permutation and duplicate checks were unrun in that
baseline. The earlier clone-based fixture was withdrawn before execution.

The first fixed batch passed Clippy, four comparator controls, all three
unchanged default startup checks and all 40 type tests. Its Core group selected
222 tests and passed 219, failing three exact-work assertions. Source inspection
and independent review initially attributed those differences to reserved-source
scans alone. That attribution was incomplete: the next actual run stopped at its
new fixture-count assertion (two modules, not three). Its Clippy passed; later
tests were unrun. The final accounting distinguishes module/nominal scans from
the separate paid scalar-preflight owner-authentication record, even when its
table is empty. Fresh separate validators directly measure both phase deltas
before the original measured/exact/one-short/retry transactions. The respective
source scan counts are two, one and one, each plus one authentication record.
Production validation and all global limits remain unchanged. No broad
retained-base execution is claimed from the source diagnosis.

The first fixed receipt records the last nested `running 1 test` as its selected
count. Its outer raw summary is authoritative for the 222-test group. The final
runner records the first outer selection and every encountered count, excluding
nested helper runs from distinct coverage. The first fixed inventory command
completed with 222619 bytes and exact 2204 names, but lacked its own timeout and
output cap; the final controller adds a 30-second/1-MiB bound and owned cleanup.
An intermediate formatting-only freeze was withdrawn without execution and all
unrelated child formatting was restored before the final freeze.

The final fixed-04 batch passed Clippy (`--lib --tests -- -D warnings`) and all
341 distinct selected units across 351 outer test occurrences. Its fresh
2,204-name inventory gates the exact selector union. The three unchanged default
startup controls passed both individually and in their module: two-owner
327335, nested cleanup 320427 and dependent discard 324976, each below 327680.
The final artifact is 807001480 bytes, SHA-256
`bb295ff4ab0957405733a4a2450772945c5e0798a463b79d8a3e8fc1bc107c31`.
All final phases have equal before/after 5,317-file maps
(`681dcfdb808ca74e10797563e991c388be0015f86b3d18ba5bf835a9932a1c2f`)
and 608 runtime-file maps
(`ff0aaab63605c2666003ae26c7d979a46c8693201be56132a0a6b4252fc63e4d`),
equal tool pins, reaped children and observed absent owned groups. Sampled target
use peaked at 6867402752 bytes; available RAM reached a sampled minimum of
8507613184 bytes. No resource stop occurred. The nested Core helper contributes
no additional distinct coverage; one name/ok pair is split by its output.
The bounded final inventory call completed with 222619 bytes in 0.102 seconds.

[`index.json`](index.json) maps original target-relative paths to deterministic,
deduplicated gzip objects. JSON records share exact source maps through local
map references; subsequent maps retain changed-path deltas against a full base.
[`verify.py`](verify.py) reconstructs every original byte sequence and verifies
its original SHA-256 and byte length without invoking Cargo or Ash. These include source maps, commands,
tools, raw output, receipts, resource samples, process records and source patches;
no compiled binary or cache is copied into the repository. Tested task and plan
snapshots preserve their pre-update bytes. Later task/evidence prose is qualified
as post-test material, not a new uniform tested source map.

Baseline Cargo was waited and reaped; its original runner did not retain a
contemporaneous group-after snapshot. Final phase records explicitly observe
owned-group absence after reaping. Resource figures are sampled observations.
Full F3 acceptance, PR110's unresolved dependency-image budgets and the connected
F-core checkpoint remain separate and pending. PM schedules F-core; the
developer runs it.

The existing [row semantics](../../../../spec/static-semantics.md) govern this
implementation correction. See [TASK-0051](../../TASK-0051-checked-ffi-contract-carriers.md)
and [issue #114](https://github.com/dikini/ash-lang/issues/114) for scope and
remaining milestone work. No specification transition is introduced.
