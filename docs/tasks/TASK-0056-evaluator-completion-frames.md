# TASK-0056: Evaluator completion frames

- ID: `TASK-0056`
- Status: active
- Related: [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md),
  [execution plan](plans/evaluator-completion-frames.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

The current effect and region specification and the accepted explicit-machine
decision govern this work. The independently reviewed plan supplies the
implementation and evidence sequence. Main integration has a separate gate.

## Work

Remove allocation-count growth from retained consumed clause completions in
allocator suffix transfers. Preserve exact deferred effect traces, capability
cuts, allocator position, ownership, cleanup and source results. Keep the
implementation within the existing evaluator machine.

## Progress

The candidate groups adjacent consumed completions with the same handler and
resume identity. Focused checks and measurements passed on the candidate. The
first independent source review found no actionable issues; final review of the
measurement receipts and committed source remains pending. The fresh workspace
checkpoint and Main integration remain separate gates.

## Verification

- Reproduce the growth regression and check sequential and tail-recursive
  controls, physical capture accounting, exact traces and failure paths.
- Run the affected effect, region, cleanup and native-storage suites named in
  the execution plan. Measure the same retained workloads and compare paired
  optimized standalone evaluator hosts, with source and binary pins.
- Obtain independent review, resolve findings and run a fresh one-job
  `cargo xtask verify` at the assigned checkpoint before Main integration.
- Record the delivered scope, remaining obligations and acceptance after the
  retaining result is verified. Main integration requires separate authorization.

## Discoveries

All 14 baseline and candidate effect traces matched byte for byte. The candidate
kept the original allocator-call and logical-completion counts. With a 336-byte
frame, tree-9 moved 88,074 suffix records instead of 10,621,975; list-1000 moved
33,029 instead of 16,071,047. Their maximum suffixes fell from 5,131 to 24 and
from 7,009 to 8 records respectively. Sequential-128 fell from 8,772 to 516
total suffix records, with a maximum of 4 instead of 132.

In nine interleaved fresh-process samples on CPU 2, median user-plus-system CPU
time fell from 430.050 to 35.950 ms for tree-9 and from 638.919 to 34.001 ms for
list-1000. These standalone hosts embed checked Core and the evaluator. In a
separate malloc-family run, tree-9 cumulative requested bytes fell from
3,651,441,363 to 106,567,107; peak usable live storage fell from 7,827,008 to
4,703,112 bytes. Cumulative requests, live storage and process RSS are distinct
measurements. Raw samples, commands and source/binary pins remain in the working
evidence for the live review.

## Deviations

None. Return any semantic gap to the governing design or proposal.
