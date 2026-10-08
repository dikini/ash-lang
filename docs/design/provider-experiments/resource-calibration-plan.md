# Resource allowance calibration plan

This is a TASK-0035 experiment under [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
It estimates compiler-resource policy; it defines no Ash semantics and accepts
no optimization or production limit change.

The collection and review batches are complete. The
[calibration report](resource-calibration/README.md) records the evidence and
remaining policy decisions. No production allowance was selected. The later
language-level attribution instrumentation below remains planned. A bounded
structural prediction/Rust reference and eight existing Ash fixtures have now
completed using the existing ledgers; see the report. No optimizer resumed.

The user's later direction permits incremental allowance evaluation. The
completed measurements used fixed diagnostic allowances and immutable input
predictors; the [report](resource-calibration/README.md#incremental-limit-evaluation)
records incremental control as the next design option, without changing those
receipts or implementing a new policy.

## Goal and baseline

The user authorized this work on 2026-10-08: return to the best retained
baseline, estimate allowances from program size and complexity, measure time
and memory, then decide how to continue.

Use `ef7956a318dee7acef43dae45923902c6181839c`, whose executable source is the
retained Original `eee40a1` / Common `5a1da1c` baseline. The latest native
preparation passed focused integration and Clippy; the preceding `2a0595d`
checkpoint has the last complete workspace gate. No full gate is claimed for
the latest baseline. The rejected producer
stays at recovery `7af4f89`. Other worktrees, draft files and recovery history
remain intact. Calibration held Common's exclusive compiler window for the
completed collection and returned it after the checkpoint. A second reserved
window completed the paired reference and supplemental fixture round; it has
also been returned. Future execution
requires another coordinated window; optimization remains paused.

The five realistic SQLite programs require the separately preserved adapter
and fixture snapshot at `11de19c8`. Apply the exact `measurement-inputs.patch`
and `native-forwarding-overlay.patch` from the
[previous cost checkpoint](common-cost-checkpoint-2026-10-08/README.md), and
record their hashes. Those inputs are experimental dependencies, not a claim
that the integrated baseline already contains the SQLite delivery.

## Measurement design

Use a compile-time experimental `resource-calibration` feature. With the
feature disabled the ordinary limits and behavior remain unchanged. With it
enabled, an explicit bounded diagnostic allowance permits completion of the
baseline workloads; report both that allowance and each ordinary allowance.
No allowance is inferred from already-expanded analysis state.

Report one compact structured record at the end of each measured phase:
loading/parsing, resolution, source checking, module linking, linked-interface
validation, final elaboration, independent Core validation, and evaluation.
Keep existing work ledgers separate. Report completed versus aborted phases;
an aborted count is not a completed cost. Avoid per-node logging and sampling
inside charged operations.

Measure phase wall time and resident memory at boundaries. Boundary RSS is
not a phase peak, and process high-water RSS is cumulative. An external
fresh-process runner records wall/CPU time and whole-process peak RSS without
including Cargo compilation. Memory accounting names its units and ownership;
it does not claim exact live-heap or allocation totals.

Measure actual execution separately from admission charges. Existing ledgers
include visited structures, comparisons and precharged storage capacity; they
are not instruction counts. GNU time records target CPU at centisecond
precision. Native-precision child CPU deltas from `getrusage` supplement it;
those deltas include the timer wrapper and its reaped descendants. Hardware
performance counters are unavailable on this host. Source descriptors predict
cost; they never substitute for an execution measurement.

Use the same optimized binary with observation enabled and disabled to estimate
observer overhead. Both modes use the same explicit diagnostic allowances.
Batch compilation once, then reuse artifacts. Fresh processes isolate cases;
warmup and repeated timed observations are labeled separately. Pin source,
compiler, build profile, executable hash, inputs, output and success/failure.

## Size and complexity

Measure the loaded input graph once, before inference: module count, UTF-8
bytes and structural source descriptors. Record each generated
family's independent parameters, including declaration width, type nesting,
polymorphic occurrences and interface/route depth. Bytes alone are insufficient.
Expanded Core and analysis sizes may explain observed costs but must not
silently enlarge their own admission allowance.

Include the unchanged five SQLite programs and orthogonal generated families:
flat declaration width, polymorphic/type depth, interface summary/route
composition, and repeated resource use where supported by the retained syntax.
Use several sizes, reserve larger sizes for validation and bound individual
runs by an external timeout. A rejected generated program is not a successful
scaling observation.

Estimate phase-specific size/complexity envelopes using completed measurements.
Compare a simple size model with a model containing explicit complexity terms;
report residuals and held-out coverage. Check whether costs grow linearly,
quadratically or faster along each family before selecting terms. Do not hide
an explosive recurrence with a permissive fitted polynomial.

Any proposed allowance includes stated headroom and a finite absolute cap.
The estimate describes only sampled families and sizes. It is neither a proof
of a universal bound nor an implementation of a new admission policy. Keep
work, latency and peak-memory evidence separate when recommending next steps.

## Delivery batches

1. Create the isolated baseline and preserve exact input provenance; add the
   feature-gated observation hooks and the fresh-process measurement runner.
2. Compile release CLI and selected native integration binaries together. Run
   a small connected smoke batch, verify normal feature-off behavior, and
   authenticate original native assertions and historical baseline work totals.
3. Run realistic and generated scaling families with repeated observations and
   observation-off controls. Fix only measurement defects or invalid fixtures.
4. Derive provisional models, review time/memory/growth evidence, document what
   is and is not supported, and preserve an unsigned checkpoint. Return the
   compiler window and stop before another optimization or production-policy
   change.

## Verification

Use original native assertions, executable integration and generated scaling
cases. Test malformed/incomplete measurement records, finite allowances and
observation-off controls through the connected batch. Avoid a new granular
compiler test inventory. Check formatting, changed documentation links,
source/input hashes, restoration and ledger ownership. A full repository gate
is required before any shared implementation retention, not before collecting
isolated experimental measurements.

## Language-structure follow-up

The user's later direction requires measures meaningful from the language's
point of view. Treat programs as controlled witnesses, derive the structures
from current judgments, and measure their implementation cost separately.
Use the user's distinction: budget predicts typical cost, work measures actual
processing, and limit determines whether checking continues. Compare budget
and work in the same units for the same processed structure. Existing charged
units include reservations, which must remain separate from actual processing.
This is a measurement-design follow-up, not authorization to restart an
optimization or choose a production allowance. Keep the retained baseline and
use one Cargo build job in a coordinated window.

### Structures and meanings

| Structure | Language-level measure | Separate implementation observations |
| --- | --- | --- |
| Monotypes, kinds and schemes | Unary application/tuple/function shape, depth and branching; ordered binder kinds; substitution domain and argument structure | Actual node visits, comparisons, copies and retained bytes by operation; capacity reservations separately |
| Rank-1 instantiation and callable composition | Scheme occurrences, ordered Type/Row arguments, composition depth/fanout and distinct lexical creations | Actual instantiation/substitution passes, analysis context creations/reuses and transfer attempts |
| Constraint evidence | Complete interface goals in their exact selection context; ordered prerequisite edges, branching, repeated goals and active cycles | Actual candidate tests, matches, prerequisite visits and evidence records retained |
| Effect rows and handlers | Exact effect instances, argument structure, row members/lacks relations and handler nesting | Actual row comparisons/substitutions, continuation-flow passes and retained control facts |
| Resource dependencies | Acquisition identities and scope nesting; dependencies through selected fields, captured values and actual calls; stored versus request-carried obligations | Actual dependency propagation, failed/repeated transfers, owner queries and live analysis storage |
| Recursive bindings | Members, binder-reference edges and cycle structure; rigid self-instantiation and guarded initialization obligations | Fixed-point rounds, new facts versus repeated visits, queue/storage growth; no runtime unfolding charged as static work |

The sources of these meanings are
[kinds and schemes](../../../spec/static-semantics.md#kinds-monotypes-and-schemes),
[rank-1 inference](../../../spec/static-semantics.md#inference-and-rank-1-restrictions),
[evidence selection](../../../spec/static-semantics.md#constraint-satisfaction-and-checked-evidence),
[effects](../../../spec/static-semantics.md#effects),
[resource dependencies](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies),
and [recursive Core structure](../../../spec/elaboration.md#recursive-binding-structure).
Implicit source instantiation and explicit Core instantiation are distinct
from structural unary type application; measure both under their
[elaboration contract](../../../spec/elaboration.md#explicit-rank-1-operations).
General foreign providers remain DN-0036 experiments, not current language
rules.

These are proposed measurement units, not new normative complexity guarantees.
Define identity and scope for every count before instrumenting it. Equal types
alone do not identify equivalent lexical creations, evidence environments,
owner identities or required analyses. Record both obligation occurrences and
any proved reusable facts; do not assume they may be merged.

### Ordered batches

1. Define the metric protocol against those judgments and the current checker.
   For each measure, state its type, identity, scope, owner, unit and discovery
   point. Separate source facts, rule obligations, actual executed visits,
   retained data and reservations. Audit counters against their operation;
   preserve CPU/time/RSS as direct execution measurements. Emit compact phase
   summaries rather than per-node logs.
2. Study rank-1 callable composition with resource-dependent captures first,
   because the prior copying census places most Invoke contexts at type
   applications returning functions. Independently vary composition depth,
   fanout, Type/Row argument shape and captured-port count. Compare reuse of one
   lexical creation with distinct creations of the same type; retain owner
   identity and actual-call distinctions. Use terminating witnesses with
   checked results and matched controls. A population census is a reason to
   investigate this family, not proof that it causes the elapsed cost.
3. Study constraint prerequisite depth/branching and repeated complete goals,
   with exact lexical evidence contexts recorded. Pair valid selections with a
   bounded active-cycle rejection. Separately study recursive term groups with
   fixed rigid types, varying members/backedges and capture propagation. The
   language does not fresh-instantiate a recursive self-use or recursively own
   its body in the Core arena. Do not substitute runtime call depth for static
   structure or assume that analysis rounds are language-required unfoldings.
4. Cross the dominant dimensions with effect-row/handler and acquisition-scope
   depth. Include copied results and dependent closures, with a corresponding
   escape/control rejection where needed. Determine whether costs combine
   additively or multiply; avoid a large undirected Cartesian test inventory.
   Rerun realistic SQLite witnesses as integration evidence, reserving new
   witnesses for validation of any revised model.
5. Use the initial rough budget procedure below as the first reference. Compare
   observed work with prediction for the same processed facts, separately from
   stopping policy. Use new families/compositions for validation; repeated runs
   measure execution noise, not additional independent language examples.
   Version fitted models. Defer Bayesian inference and richer predictors until
   a practical decision needs them.
   Separately evaluate limit policies and what justifies an allowance adjustment.
   Report which growth follows increasing
   language obligations and which comes from representation expansion or
   repeated implementation work. Preserve uncertainty where attribution is
   incomplete. Then choose whether the evidence calls for policy adjustment,
   an implementation change, or language-design investigation.

Each execution batch should reuse one optimized build, run connected e2e and
integration witnesses, measure observer overhead and preserve completed versus
refused outcomes. Add regression tests only for demonstrated defects. A metric
or candidate is useful when it enables a stated decision with transferable
evidence, not merely when it predicts one SQL program's counter.

## Initial rough budget procedure

The user's latest direction selects a simple first estimator. Its offline
implementation and descriptive comparison are complete in the linked report.
Use the completed
44-case CPU-precision round to recalibrate a four-term nonnegative polynomial:

```text
budget = a + b*surface_nodes
           + c*(type_nodes*type_depth)
           + d*(resource_sites*surface_nodes)
```

Fit separate point predictions for CPU seconds, peak RSS KiB and each of the
six reservation-including ledger charges. Fit per-case medians; do not include
headroom, residual cushions or refusal ceilings in the budget. Record the
training input hash, coefficients, units and prediction errors. This is an
offline reference, not compiler limit enforcement. Previously examined
held-out cases now become explicit recalibration data; never present them as
fresh validation of the new fit.

Use the eight existing fixtures for a descriptive transfer check without
refitting. Report poor predictions and observations outside recorded feature
ranges. Do not add more features, a family classifier or a Bayesian model to
rescue this first estimate. The language-level attribution plan remains useful
if this rough reference fails to explain a material cost.
