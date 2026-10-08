# Retained-baseline resource calibration, 2026-10-08

This is isolated [TASK-0035](../../../tasks/TASK-0035-resource-analysis-relevance-and-fusion.md)
evidence under [DN-0036](../../DN-0036-foreign-library-and-memory-provider-experiments.md).
It changes neither Ash semantics nor production resource policy. Further
optimization is paused pending review of these results.

## Finding

The retained compiler executes the realistic SQLite cases with median wall
times of approximately 0.06–0.23 seconds and 22–42 MiB process peak RSS on this host. Copying and
persistence exceed ordinary admission charges despite these modest observed
costs. The old numerical ceilings were not calibrated against these programs.
There is no evidence here that their practical execution cost requires another
optimization before delivery.

Input size alone is a poor allowance predictor. A flat program with 1,546
surface nodes incurs 10,301 Source charges; copying has 1,480 nodes and
1,212,707 charges, about 118 times as many. Adding the measured complexity
terms improves Source coverage but still misses copying and bound NUL. These
fits cannot serve as general resource-program admission rules.

## Baseline and scope

The worktree starts at `ef7956a318dee7acef43dae45923902c6181839c`, with executable
source equal to retained Original `eee40a1` and Common `5a1da1c`. The rejected
producer `7af4f89` is excluded and preserved in its recovery branch. No worktree
was destructively reset. [Baseline provenance](baseline.json) pins the source
and two experimental SQLite input patches from recovery `11de19c8`.

Those patches supply the real SQLite library, adapter and native assertions;
they are separate experimental dependencies. The measured compiler also has
feature-gated observation hooks and a finite diagnostic allowance. It is not
an unmodified production binary or a newly verified SQLite delivery.

The latest retained executable preparation had focused integration and Clippy
verification. The preceding `2a0595d` checkpoint had the last complete workspace
gate. This calibration does not claim a new full workspace gate or authorize
merging experimental inputs into shared implementation.

## Measuring actual work

These quantities remain separate:

| Quantity | Measurement | Meaning and limits |
| --- | --- | --- |
| CPU execution | Native-precision `getrusage(RUSAGE_CHILDREN)` deltas | Actual user plus system CPU consumed by the timer wrapper and reaped target descendants; excludes the Python runner. It is not a machine instruction count. |
| Elapsed time | Target GNU time and per-phase monotonic timers | GNU time has centisecond formatting; phase timers retain nanoseconds. Wall time includes scheduling and I/O delays. |
| Resident memory | Whole-process peak RSS; `/proc/self/status` at phase boundaries | Peak RSS includes libraries and allocator retention. Boundary RSS is not a phase peak, live heap size or allocated-byte total. |
| Admission charges | Six existing ledger endpoints | Counts visits, comparisons, retained records and precharged storage capacity. These are policy charges, not literal operations or physical memory bytes. |
| Input descriptors | One pre-inference surface graph traversal | Immutable size/complexity predictors; they never substitute for measured execution. |

For example, [evidence indexing](../../../../src/core/capture/value.rs)
precharges maximum table capacity even when duplicate keys need fewer entries.
Context path conversion charges `3 * length + 1` for storage, traversal and
reversal. Other charges closely follow executed kind traversals or comparison
attempts. Adding these heterogeneous charges does not produce an instruction
count. Hardware performance counters were unavailable: the host denied the
`perf` probe with `perf_event_paranoid=4`; no system policy was changed.

The six reported owners exclude graph-wide interface constraints, separate
builder/rewrite and coverage budgets, syntax and runtime budgets. Their totals
are not the complete work of compilation. The diagnostic override reaches
some unreported owners too; this round does not calibrate every existing limit.

## Collection and verification

Release compilation occurred once in a connected batch, followed by one
additional generated-resource test build. Measurements invoke those exact
artifacts directly; build time is excluded. The same binary runs with
observation on and off and the same diagnostic base allowance of 16,777,216
units; Core retains its threefold allowance of 50,331,648. The ordinary
327,680 / 983,040 constants remain unchanged.

The corpus contains 44 programs: flat declaration width, nested types,
prerequisite depth, public reexport width/depth, string payload size, repeated
resource scopes and five unchanged realistic SQLite cases. Twenty programs
train the models; 24 are held out, including all five SQLite programs.

Each full round has one warmup and three measured fresh processes per mode:
352 processes, including 264 measured and 88 warmups. The first round supplied
the initial fits. A second round added finer CPU measurements of the same
corpus. Both rounds completed every case with zero failures. This replay is a
measurement replication, not a new independent validation set. A prior
12-case smoke batch also passed both modes.

The native runs execute exactly one named test each and retain original
database values, persistence/reopen, completion and release assertions. The
runner rejects zero-test success, malformed records, missing/aborted phases,
changed inputs/artifacts and timeout. A connected Python self-check covers
those measurement failures. Feature-off release library checking passed;
format and evidence checks are recorded in the capsule. There was no full
workspace gate for this isolated experiment.

The host was Linux x86-64, AMD Ryzen 7 7435HS, 16 logical CPUs; Rust 1.97.1,
LLVM 22.1.6, optimized release profile. These are local desktop measurements,
not cross-machine performance guarantees. Three repetitions report observed
ranges, not statistical confidence bounds.

## Actual time and memory

These are observation-off medians from the CPU-precision round. Parentheses
show the three-run CPU range. CPU includes the timer wrapper; target wall time
and peak RSS come separately from GNU time.

| SQLite case | Actual CPU seconds | Target wall seconds | Peak RSS MiB |
| --- | ---: | ---: | ---: |
| Copying | 0.184 (0.180–0.215) | 0.18 | 33.57 |
| Persistence | 0.229 (0.228–0.259) | 0.23 | 42.38 |
| Resume | 0.062 (0.061–0.066) | 0.06 | 22.54 |
| Bound NUL | 0.182 (0.179–0.184) | 0.18 | 33.50 |
| Forwarding | 0.064 (0.063–0.065) | 0.06 | 22.15 |

Small programs consume real CPU even when GNU time prints `0.00`: flat width
one consumes a median 6.5 ms of wrapper-inclusive child CPU; width 128 consumes
25.0 ms. These measurements include startup, rendering and teardown. They
must not be interpreted as pure checking costs or infer asymptotic complexity
from such small totals.

The flat-width/copying comparison illustrates the distinction: about 118 times
the Source charge corresponds to about 7.3 times the measured whole-process
CPU, or 16 times the observed Source wall time, in this round. These are
different programs and costs; there is no universal conversion from a charge
unit to CPU time.

Input collection traverses each finite surface module once; it does not unroll
recursive calls. Actual checker timing includes every traversal, context
expansion or repeated analysis the implementation executes. Runtime recursion
belongs to the separately timed evaluation phase. Recursive call structure
was not an independent scaling axis in this corpus, so the estimates do not
characterize that dimension.

For compiler allowances, complexity means the checking work induced by source
structure. Runtime algorithmic complexity is a separate axis: executing one
recursive function many times need not require equivalent static unfolding.
Similarly sized sources can induce different instantiation, constraint and
capture-analysis costs. The present aggregate descriptors do not establish
which of those dimensions explains the observed gap.

The phase timers separate compilation from evaluation. In the first full
round, evaluation consumed 0.4–1.8% of pipeline time. Copying's median Source
time was 96.6 ms, about 52% of its pipeline; Core was 55.5 ms, about 30%.
Persistence's Source was 55.1 ms, about 26%; Core was 105.3 ms, about 49%.
Persistence has half copying's Source charge but is slower overall because its
Core and final-elaboration costs are larger. Source charge alone cannot rank
total compiler cost.

Whole-process peak memory also needs separate interpretation. Copying's
high-water RSS is already near its final peak during Source checking.
Persistence rises substantially during Core validation. Cumulative visits
cannot establish peak live memory or isolate temporary allocations.

Observation-on/off CPU median differences for the five SQLite programs range
from approximately −0.1% to +7.2% in the precision round. Small negative
differences reflect measurement variation, not negative observer cost. Both
modes retain feature-enabled allowance machinery. This comparison does not
measure that machinery against a separately built ordinary executable.

## Charges and allowance estimates

The median charge vector preserves the previous baseline, allowing small
fresh-process capacity variations where recorded. Source and Core ownership
remain separate; repeated per-module cumulative counts are never summed.

| Case | Source | Final elaboration | Independent Core | Ordinary-limit deficit |
| --- | ---: | ---: | ---: | --- |
| Copying | 1,212,707 | 165,717 | 903,995 | Source |
| Persistence | 597,882 | 376,641 | 1,609,087 | Source, final elaboration, Core |
| Resume | 203,215 | 103,738 | 289,063 | None in these three owners |
| Bound NUL | 1,212,707 | 165,717 | 903,990 | Source |
| Forwarding | 216,584 | 107,066 | 315,193 | None in these three owners |

The estimator uses each case's maximum raw charge, nonnegative coefficients
and a training-only positive residual cushion. It freezes all coefficients
and cushions before collecting held-out cases. Independent review found exact
agreement between frozen and completed values for all 24 phase/model pairs.
Fitting requires full column rank, sufficient samples and multiple families.

Each provisional envelope is
`min(16_777_216, ceil(2 * max(1, prediction + training_cushion)))`.
The twofold headroom and absolute cap are explicit experimental choices, not
calibrated production recommendations. No held-out miss was caused by clipping
at the cap. Raising that cap would not fix the inadequate predictions.

Let `n` be surface nodes, `T = type_nodes * type_depth`,
`I = imports * module_depth`, and `R = resource_sites * n`.
The Source interaction prediction is
`12.1522*n + 35.9890*T + 2.99266*I + 18.9161*R`, with cushion `31522.5643`.
It proposes approximately 353,396 units for copying against 1,212,707 observed.
The full equations, residuals and per-case coverage are preserved in the JSON
evidence; rounded numbers here explain the result rather than define policy.

| Owner | Simple size coverage | Interaction coverage | Remaining interaction misses |
| --- | ---: | ---: | --- |
| Resolution | 24/24 | 24/24 | None in this corpus |
| Module linking | 24/24 | 24/24 | None in this corpus |
| Linked interface | 21/24 | 21/24 | Persistence, resume, forwarding |
| Source | 21/24 | 22/24 | Copying, bound NUL |
| Final elaboration | 19/24 | 19/24 | All five SQLite cases |
| Independent Core | 18/24 | 18/24 | All five SQLite cases, 64 KiB string |

A separate type-depth model covers 23/24 linked-interface cases, missing
persistence. No model covers realistic final-elaboration/Core costs adequately.
Resolution and linking estimates remain provisional within the sampled domain.

## Growth and interpretation

- Flat Source charges increase exactly 80 units per added function across
  widths 1–128; final elaboration adds 84 and Core adds 105.
- Nested type and prerequisite families have positive constant second
  differences over depths 8/12/16, supporting a quadratic component in this
  tested range. This is not an asymptotic proof.
- Resource scope totals include a large fixed library cost. Marginal Source
  charges per additional scope increase from 5,956 to 6,183.5 over the measured
  widths; sublinear total ratios do not establish linear scaling.
- String payload produces exactly `payload_bytes + 152` Core charges in the
  three sampled programs. The models record but omit payload bytes, explaining
  that predictable held-out miss. Source and final charges stay constant.
- Reexport depth increases resolution and checking while leaving final/Core
  charges unchanged in this family. One allowance formula for every phase
  would hide this distinction.

The data establish missing predictors, not the cause of copying's amplification.
Callable composition, branching, handlers and provider operations are possible
dimensions to investigate. Claims about their individual contribution require
controlled families or attribution evidence.

Keep the retained baseline. The next decision should distinguish a practical
CPU/memory requirement from an admission-policy requirement before selecting
another optimization. Any revised source predictor must be tested against new
programs, since this held-out set has now been examined.

## Incremental limit evaluation

The user's follow-up proposes evaluating limits incrementally. A whole-program
estimate before checking is not required. The unsuccessful fits above test one
possible predictor; their failure does not prevent incremental control.

Current structural ledgers already accumulate charges as checking proceeds.
The next design can evaluate whether to continue at phase or bounded-work
checkpoints, and can refine an allowance as relevant source, type and
constraint structure becomes known. Size and complexity then inform policy
and explain observed costs without requiring a complete cost prediction at
entry. A configured CPU or memory ceiling can also be checked incrementally
without a size-based prediction.

The design must distinguish consumed charges, measured execution costs,
discovered complexity facts and the allowance decision. In particular, it
should say which discovered facts justify an adjustment and which represent
work consumed. This lets us assess both expensive legitimate programs and
unnecessary expansion using the same measurements. Report the reason for
continuation or refusal and the selected finite overall policy.

This is a design option, not implemented control. The current observers emit
phase endpoints; the collector obtains whole-process CPU/RSS after execution
and enforces an external timeout. It does not periodically enforce CPU or
memory limits inside a phase, nor adjust allowances during checking. Moving to
incremental evaluation needs checkpoint placement, ownership, measurement
overhead and failure/retry behavior to be reviewed. The
[specification](../../../../spec/static-semantics.md#failure-ownership-and-constraint-resources)
already separates bounded compiler policy from Ash value semantics and requires retry
with sufficient work to agree with a fresh run.

## Evidence and reproduction

[The capsule manifest](manifest.json) pins compressed raw runs, generated
inputs, collector versions, compiler source hashes, artifact hashes, build
receipts and analysis. The archives omit compiled binaries; build them from
this isolated source checkpoint. Recorded local paths identify historical
inputs and need relocation for reproduction.

From this worktree, build with `RUSTC_WRAPPER=` and
`CARGO_TARGET_DIR=target/calibration`:

```bash
cargo test --offline --locked --release --no-run --features resource-calibration --bin ash --test provider_sqlite_copying --test provider_sqlite_sessions --test provider_sqlite_control --test resource_calibration_native --jobs 2 --message-format=json
```

Use the returned release binary paths with the
[corpus generator](../../../../tools/resource_calibration_cases.py), then run
the [collector](../../../../tools/resource_calibration.py) against its manifest:

```bash
python3 tools/resource_calibration.py run MANIFEST --output NEW_DIRECTORY --warmups 1 --repetitions 3 --timeout 30 --limit 16777216 --model-cap 16777216
```

The generator's `generate --help` lists the required CLI and four native test
artifact arguments. `self-check` verifies the collector without running Ash.
No estimate is applied to the compiler automatically.
