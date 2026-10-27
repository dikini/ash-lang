# Evaluator completion-frame execution plan

This temporary plan belongs to
[TASK-0056](../TASK-0056-evaluator-completion-frames.md). It translates the
reviewed implementation handoff into the active assignment;
it does not define semantics or architecture. The full reviewed handoff and its
independent review remain in the task's working evidence as
`frame-remediation-corrected-plan.txt` and `frame-plan-review.txt`.

## Selection and invariants

Use the current specification and
[AD-0008](../../decisions/AD-0008-explicit-evaluator-machine.md).
A bounded probe of the 14 retained programs selected grouping: adjacent
consumed, unregistered completions may share one physical record only when
both handler and resume identity match. Keep the exact deferred return trace.

Preserve the owner-position allocator callback and saved preceding selection,
one-shot capture and restoration, lexical instantiation, pending construction,
registration and resource ownership, cleanup order and paired release. Internal
resource failures remain terminal. No language rule, allocator bypass, general
stack rewrite or diagnostic contract change is part of this work.

## Implementation

- Initialize every clause completion count to one. Live and registered clauses
  require count one; a larger count represents adjacent consumed unregistered
  clauses with the same identity pair.
- Merge only at a successful topmost resume with an immediately preceding
  eligible record. Keep records separate if addition overflows. Complete all
  existing reservation and ownership preflight before consuming the capture.
- Emit the same number of deferred clause-return events at normal completion,
  reserving the complete group before publishing any event. Physical frame
  counts govern capture quotas; logical counts do not add owners or disposal.
- Validate impossible counts on affected return, resume and discard paths.
  Preserve nearest-pair rejection and existing registration bookkeeping.

## Evidence

- Demonstrate the growth regression before the fix. Check sequential and
  tail-list results, allocator and context requests, logical returns, physical
  completion and suffix storage, and evaluator depth across retained sizes.
- Check differing identities, live and registered predecessors, intervening
  work, non-tail resumes, count overflow, exact trace order, preflight failure,
  physical quotas, nested saved segments, discard and iterative disposal.
- Run the affected effect, region, cleanup and native-storage suites. Include
  the existing custom allocator, owner-position, pending construction,
  action-local handler, refusal and paired-release cases. Preserve source and
  Core rejection of duplicate or escaping resume capabilities.
- On the same 14 retained inputs, record actual physical suffix counts and
  compare logical completions and complete effect traces with the baseline.
  Keep disposable diagnostic source and binaries distinct from timing binaries.
- Build the candidate compiler and three optimized standalone evaluator hosts
  from the pinned product source. Compare tree-7, tree-9 and list-1000 using one
  warmup and nine interleaved fresh processes on the recorded CPU. Check every
  output and report raw CPU, wall and RSS samples. Measure malloc-family traffic
  and usable live storage separately from uninstrumented timing.
- Record source, configuration, compiler, input and binary hashes. Describe the
  finite workloads and remaining structural work; do not present predicted
  savings or standalone evaluator hosts as native Ash code generation.

## Review and retention

Freeze the candidate, focused receipts and measurements for independent review.
Repair findings and refresh affected evidence. After focused checks, review and
measurements, the developer runs the assigned fresh one-job workspace checkpoint
before Main integration. A draft PR may show pending review and checkpoint
status. Main integration and signing remain separate gates.

After an authorized retaining result is verified, record delivered and remaining
acceptance with its owner, preserve concurrent updates and read the result back.
Retain working evidence while the PR or checkpoint needs it. Retire only owned,
obsolete artifacts under the repository policy; preserve shared caches and
unrelated work. Record cleanup result and next owner.
