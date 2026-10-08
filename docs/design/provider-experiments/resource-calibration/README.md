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
| Elapsed time | Target GNU time and per-phase monotonic timers | GNU time has centisecond formatting; phase timers retain nanoseconds. Wall time includes scheduling and I/O delays. The paired reference also records matching wrapper wall time. |
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

The historical builds used two Cargo jobs, a deviation from the coordinated
one-job policy. Their receipts remain unchanged. Future reproduction uses one
job; no rebuild or replacement of measured artifacts is implied.

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

## Existing Ash language fixtures

Eight existing positive fixtures supplement the resource corpus. Each completed
one warmup and three measurements in both observation modes, with exact outputs
and source/test provenance checked. These are ordinary language baselines,
not an application corpus. The table uses observation-on charge medians and
observation-off physical measurements. GNU wall time is formatted in 10 ms
steps; `0.00` does not mean zero elapsed time.

| Existing fixture | Source units | Final units | Core units | OFF CPU median (ms) | OFF CPU range (ms) | OFF wall median (s) | OFF peak RSS median (MiB) |
|---|---:|---:|---:|---:|---:|---:|---:|
| Higher-order application | 180 | 200 | 326 | 9.734 | 6.401–10.518 | 0.00 | 12.28 |
| Global recursive scope | 238 | 262 | 377 | 6.795 | 6.509–7.129 | 0.00 | 12.31 |
| Local recursive scope | 166 | 180 | 388 | 7.417 | 7.016–8.619 | 0.00 | 12.08 |
| Combined effects/rows | 5,159 | 3,936 | 1,993 | 13.596 | 10.355–13.784 | 0.01 | 14.22 |
| Newtype facade | 275 | 197 | 346 | 7.031 | 6.692–7.299 | 0.00 | 12.29 |
| Higher-kinded linked | 1,390 | 765 | 783 | 7.902 | 7.803–8.354 | 0.00 | 14.26 |
| Polymorphic methods | 5,486 | 3,206 | 4,147 | 10.222 | 9.685–11.527 | 0.00 | 15.10 |
| Relational module bundle | 9,244 | 4,101 | 5,032 | 15.936 | 13.284–16.874 | 0.01 | 14.86 |

All six reported ledgers remain below their ordinary limits in these fixtures.
Global/local recursive examples exercise simultaneous scope and retained
recursive references; their executed path terminates without invoking the
retained back-reference. They do not measure deep runtime recursion or scaling
in recursive checker obligations. The repository still lacks an established
basic application corpus of parsers, data pipelines and substantial algorithms
for this comparison.

The original supplemental manifest declared pinned test source hashes but
omitted their snapshot paths. The collector correctly rejected all 64 records
for incomplete provenance snapshots, although outputs and file hashes agreed.
Adding the missing paths corrected the manifest; the 64-process rerun passed.
Both rounds remain preserved, and rejected records stay excluded from estimates.
The paired and supplemental collection therefore used 256 processes instead
of the planned 192, with 192 valid and 64 rejected. Serial execution including
review and correction finished in 95.6 seconds, within the frozen 180-second
window. Common's compiler window has been returned; no further engines ran.

## Budget, work and limit

The user's terminology distinguishes three roles:

- A **budget** predicts how much a language structure should typically cost.
- **Work** records how much processing actually occurred; CPU/time/memory
  record corresponding execution costs in their own units.
- A **limit** controls whether checking may continue. Headroom and stopping
  thresholds belong to this policy, not to the typical-cost estimate.

Existing implementation names such as `TypeWorkBudget` refer to bounded
accounting. Keep their recorded charges distinct from a new predictive budget
and from executed-operation counts: their reservation component prevents
calling every charged unit actual processing. The next instrumentation must
separate those components before fitting a language-level work budget.

For the known witnesses, measured medians provide reference costs. They are
not general budgets for other structures. The initial fitted envelopes below
include cushions/headroom and were evaluated as possible allowances; they
must not be relabeled typical-cost predictions.

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

Budget evaluation can also be incremental. At a checkpoint, compare observed
work with the budget for the same processed language structure. Record both
`work - budget` and `work / budget` where the budget is positive; keep an
unfinished obligation separate. The budget may change as new relevant
structure is discovered. A stopping decision remains a separate limit policy.

## Language-level measures

The user's next clarification sets the unit of study: language structures and
their checking obligations. A program is a witness of those structures, not
the definition of complexity. Surface node totals and the five SQLite programs
alone cannot justify a language-wide allowance or checker design.

The [follow-up measurement plan](../resource-calibration-plan.md#language-structure-follow-up)
derives measures from current type instantiation, evidence selection, exact
effect instances, recursive bindings and resource-dependency rules. It pairs
those structures with actual implementation visits, retained structures and
CPU/RSS. This separates the question "which obligations arise?" from "how
much work does this checker perform to discharge them?" without assuming that
every repeated obligation is redundant.

These measures may be discovered incrementally. No complete static expansion
or runtime-recursion unrolling is required before checking begins. The next
decision needs controlled variation of depth, branching, reuse and lexical
identity, plus realistic end-to-end witnesses. The new attribution instrumentation remains planned. The bounded structural
reference below is complete using existing charged ledgers; it does not
implement the distinction between executed visits and reservations.

## Structural predictions and Rust reference

The follow-up reused the same optimized Ash executable without rebuilding it.
A protocol froze four empirical charged-cost curves before execution, using
prior completed depths 1, 2, 4, 8, 12 and 16:

```text
Nested type Source(d) = 15*d^2 + 272*d + 386
Nested type Core(d)   = 28*d^2 + 269*d + 451
Prerequisite Source(d) = 25*d^2 + 346*d + 2165
Prerequisite Core(d)   = (157*d^2 + 623*d + 1752) / 2
```

All 20 Source/Core predictions matched the observed ledgers at depths 1, 4,
16, 24 and 32. Eight predictions concerned the previously unmeasured depths
24 and 32. No coefficient was refitted. This confirms these charged-cost
curves over the extended tested range. It does not prove asymptotic bounds,
predict arbitrary compositions or explain SQLite's amplification. These are
predictions of heterogeneous charged units, not a new count of actual
executed operations or a CPU/memory budget.

Fourteen pairs match flat declaration width, nested algebraic types with
polymorphic identity use, and recursive interface/trait prerequisites. Width
zero supplies a startup control. Rust uses a custom Option type and explicit
generic trait implementations; its result is checked by a separate untimed
native harness with all 14 assertions. The timed Rust command emits library
metadata without LLVM, object generation or native linking. It includes
resolution, type/trait and MIR borrow checking plus metadata encoding. This
boundary follows the pinned [Rust 1.97.1 analysis implementation](https://github.com/rust-lang/rust/blob/1.97.1/compiler/rustc_interface/src/passes.rs#L1062)
and [output configuration](https://github.com/rust-lang/rust/blob/1.97.1/compiler/rustc_session/src/config.rs#L809).
Ash includes its own checking, independent Core validation, evaluation,
rendering and teardown. These shared structures permit a useful reference;
the compilers do not perform equivalent work. Rust work-unit counters are
unavailable and are not inferred from time.

Selected observation-off CPU medians and three-run ranges, in milliseconds:

| Structure | Ash CPU ms (range) | Rust CPU ms (range) | Ash / Rust peak RSS MiB |
| --- | ---: | ---: | ---: |
| flat-width0 | 9.2 (6.1–9.2) | 31.5 (31.2–34.1) | 12.10 / 57.16 |
| flat-width128 | 27.3 (20.6–30.8) | 50.1 (42.3–55.4) | 13.90 / 62.51 |
| nested_type-depth24 | 18.3 (15.3–19.5) | 46.2 (33.5–48.6) | 13.14 / 62.36 |
| nested_type-depth32 | 14.5 (14.5–15.2) | 35.8 (33.9–37.1) | 13.30 / 62.20 |
| prerequisite-depth24 | 18.7 (17.7–22.5) | 37.3 (35.9–39.0) | 14.84 / 68.76 |
| prerequisite-depth32 | 23.9 (23.4–28.9) | 36.9 (36.7–37.6) | 15.20 / 68.81 |

Across all 14 pairs, Ash CPU medians are approximately 7.6–27.3 ms and Rust
medians 31.5–50.1 ms. Startup contributes much of these small totals. Depth 24
nested-type timing exceeds depth 32 in this round, illustrating variation.
Report the absolute sampled costs and growth in charges; these measurements
do not establish general relative compiler efficiency or CPU complexity.
Do not subtract noisy startup medians or resident memory and call the
remainder semantic work.

The new sampler brackets a blocking wait with monotonic wall time and child
CPU measurements over the same wrapper interval. Every measured Ash process
has CPU below this matching wall measurement. Target GNU time remains a
separate measurement with 10 ms formatting granularity. Use the user's
accepted ±10 ms comparison tolerance for those displayed times; it is not a
calibration of absolute instrument error. Scheduling and I/O can increase
wall time independently of the process's CPU consumption. Repeated-run
ranges remain necessary even with finer timestamp precision.

The paired round completed 128 valid processes: 84 measured, 28 warmups,
14 Ash observers and the untimed harness build/run. Independent audit
verified every raw record, input/executable/log hash, required phase and
frozen prediction. No Cargo build, optimizer change or production-limit
change occurred.

## Initial rough budget procedure

The user selected a simple first procedure. The offline
[estimator](../../../../tools/resource_budget_estimates.py) uses one fixed form:

```text
budget = a + b*nodes
           + c*(type_nodes*type_depth)
           + d*(resource_sites*nodes)
```

`nodes` is the measured surface structure total; `type_nodes` and `type_depth`
describe surface type syntax. `resource_sites` counts lexical resource
initialization/binding sites, not dynamic operations. These existing input
descriptors are available before inference. They are rough proxies for the
language obligations identified in the follow-up plan, not the new typed
attribution measures that remain unimplemented.

Use the procedure as follows:

1. Collect completed case medians with a pinned compiler and measurement
   boundary. Keep CPU seconds, peak RSS KiB and each ledger's charged units
   separate.
2. Fit nonnegative coefficients for each response using the same four terms.
   Keep a single point estimate; do not add cushions or headroom to the budget.
3. Freeze the model and input hash. For a new measured feature vector, evaluate
   the formula and flag values outside recorded feature ranges. Being inside
   every range does not establish that a new combination is well represented.
4. Compare actual cost with prediction in the same units. Record the signed
   residual and actual/predicted ratio. Recalibrate explicitly when new evidence
   warrants it; repeated observations are not new language examples.
5. Decide stopping limits separately. The estimator neither changes compiler
   allowances nor feeds expanded work back into its own budget.

The first [model artifact](rough-budget-model.json) recalibrates on all 44
completed CPU-precision cases, including the already examined former held-out
cases. It fits per-case medians, not maxima. The
[transfer comparison](rough-budget-transfer.json) describes the eight existing
Ash fixtures without refitting. Those measurements were already examined;
this is not blind validation. Every response fit converged. Poor predictions
remain visible, with no extra feature search or family classifier.

RMSE measures absolute prediction error in each response's own units:

| Response | Units | 44-case fitting error | Eight-fixture transfer error |
| --- | --- | ---: | ---: |
| cpu_seconds | ms | 26.30 | 6.40 |
| peak_rss_kib | MiB | 2.92 | 1.24 |
| source-checking | charged units | 188,590.77 | 22,379.57 |
| final-elaboration | charged units | 36,917.91 | 1,480.73 |
| independent-effect-core | charged units | 188,455.50 | 12,943.99 |

For example, the CPU estimate is 105 ms against copying's observed 184 ms, and
175 ms against persistence's 229 ms. Predicted RSS is 25.75 MiB versus 33.57
MiB for copying, and 36.52 MiB versus 42.38 MiB for persistence. These are rough
references. The fitted CPU intercept is zero, although measured startup has a
real cost; small-program CPU predictions understate that fixed cost. Relative
error can therefore be large even when absolute error is a few milliseconds.

Ledger predictions are much weaker: copying Source is estimated at 476,786
against 1,212,707 charged units, while many basic programs are overestimated.
Neither that miss nor an excessive ledger ratio proves excessive physical
compiler cost. Use CPU and memory evidence alongside the charges when deciding
whether optimization is needed. This initial procedure is implemented; a
general calibrated budget or revised stopping policy is not.

The model is reproducible from completed evidence:

```bash
python3 tools/resource_budget_estimates.py fit SUMMARY_JSON --output MODEL_JSON
python3 tools/resource_budget_estimates.py predict MODEL_JSON FEATURES_JSON
python3 tools/resource_budget_estimates.py evaluate MODEL_JSON ANOTHER_SUMMARY_JSON
```

`FEATURES_JSON` supplies `nodes`, `type_nodes`, `type_depth` and
`resource_sites`, or a case with those fields inside `features`. The artifact
pins the estimator, existing fitter and training summary hashes. The original
allowance-envelope fits remain unchanged. Bayesian inference and richer
predictors are deferred until a practical decision needs them. Prediction
beyond the observed domain still needs confirmation; see the
[NIST guidance on extrapolation](https://www.itl.nist.gov/div898/handbook/pri/section5/pri5998.htm).

## Functional Rust SQLite reference

Five working Rust counterparts now cover copying, persistence, resume,
bound-NUL refusal and forwarding. All 60 fresh compiler jobs and ten native
validations passed in one bounded round. Median Rust metadata checking cost
98–135 ms CPU and 107–111 MiB peak RSS; complete native compilation cost
232–384 ms CPU at O0 and 434–830 ms at O3. The shared Rust bridge is compiled
in every job, and the source size is 17.8–20.2 KB versus Ash's 8.2–13.2 KB.

The [full Rust comparison](sqlite-rust.md) reports per-case CPU, wall, RSS,
source sizes, executable sizes and semantic differences. Rust lifetimes and
one-shot closures approximate the overlapping resource behavior; they do not
reproduce Ash's effect machinery or independent Core verification. These
informational results do not reopen optimization or change compiler policy.

## Evidence and reproduction

[The capsule manifest](manifest.json) pins compressed raw runs, generated
inputs, collector versions, compiler source hashes, artifact hashes, build
receipts and analysis. The original archives omit compiled binaries; build them from
this isolated source checkpoint. The separate [reference evidence index](reference-evidence.json)
authenticates the paired and supplemental rounds, generated inputs, tool bytes,
rejected records, corrected manifest and execution receipt. Original archives
and their manifest remain byte-identical. Recorded local paths identify historical
inputs and need relocation for reproduction.

From this worktree, build with `RUSTC_WRAPPER=` and
`CARGO_TARGET_DIR=target/calibration`:

```bash
cargo test --offline --locked --release --no-run --features resource-calibration --bin ash --test provider_sqlite_copying --test provider_sqlite_sessions --test provider_sqlite_control --test resource_calibration_native --jobs 1 --message-format=json
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
