# Resource allowance calibration plan

This is a TASK-0035 experiment under [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
It estimates compiler-resource policy; it defines no Ash semantics and accepts
no optimization or production limit change.

The collection and review batches are complete. The
[calibration report](resource-calibration/README.md) records the evidence and
remaining policy decisions. No production allowance was selected.

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
remain intact. Calibration owns Common's exclusive compiler window.

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
