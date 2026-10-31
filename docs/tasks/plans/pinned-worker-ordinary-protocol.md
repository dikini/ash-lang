# Pinned worker ordinary protocol delivery

This execution plan belongs to [TASK-0058](../TASK-0058-pinned-worker-network.md).
It has no independent semantic authority. The 2026-10-31 user direction
superseded protocol-specific compiler checks. The milestone's implemented
[specification](../../../spec/README.md) and
[AD-0017](../../decisions/AD-0017-pinned-worker-host-and-transport.md) record
the language boundary and host decision. Main integration remains separate.

## Connected slice

1. Start from `libraries/network_types.ash`, `libraries/network_codec.ash`,
   the existing bridge, and the unretained `paired-producing-cleanup.ash`
   fixture in the preserved `m4-receipt-emission-assembly` worktree. Selectively
   adapt that fixture's pure functional ledger, closed driver and cleanup
   handler into ordinary Ash module code; it is not present in this base. Use ordinary threaded state,
   calls and result/error cases; use a Cell only if an actual need appears.
   Retain two private closed worker entries under the existing entry rules. Do
   not invent a generalized command/session API, capability, runtime monitor
   or framework. A private wrapper does not revoke already-copied raw aliases.
2. In that program, reserve each child and queue its Work before attempting
   send. Keep pending output on Full and service incoming work and control.
   Thread the actual successor state through each ordinary operation. A stale
   saved value must not replace it. Work completion includes the actual local
   work and cleanup; only then close it and queue Ack when children are gone.
   Handle unmatched, duplicate or wrong-peer Ack as an ordinary error or no-op,
   leaving outstanding obligations. Malformed data and operation failures
   must not become success. Preserve transport obligations on failures before
   and after publication or receipt.
3. Exercise the first connected slice: root Work runs real cleanup that produces
   one registered descendant; its Ack permits parent retirement and upstream
   Ack; the driver drains, finishes, observes real End and settles. The public
   capacity-one production run must return `42` after both workers and the
   host settle.
   Do not use a Boolean, test injection or protocol metadata as a substitute
   for the existing generic Store/retained-control and native host contracts.
   If existing language or N2 facilities cannot express the actual path, record
   the precise gap and revise the governing artifact; do not add an ad hoc
   runtime checker or weaken a generic release rule.
4. Extend the same path to remaining shutdown cases and the N6 application and
   FFI gap assessment. Keep N5 closure, N6, specification integration and the
   full workspace gate separate from the first public slice.

## Migration and verification

Reconcile the existing per-delivery held tracking and the owner's empty-delivery
report requirement with the revised worker-lifetime contract: do not fabricate
an empty report. On this base, the relevant boundaries include
`Frame::NetworkReceiveCommit`, `WorkerStartup::delivery_report`,
`CarrierReport::Returned`, `CarrierGroup::settle`, the actual transport
`finish_receive` predicate, `reject_unchecked_control_references` and N2 worker
admission/completion analysis. Keep receive copy and queue-commit ordering.
`finish_receive` closes transport only; settlement still waits
for actual worker return, endpoint readiness, release, teardown and carrier
joins. Preserve failure parking, generic C3 and the existing FFI boundary.
When removing the worker-release-roots exemption, still invoke generic
retained-release checking, for example
`check_nodes_with_release_workers(..., None, ...)` or equivalent with release
checking enabled. Do not fall back to plain `check_nodes` or disable C3.

Remove unretained protocol-specific compiler machinery introduced for this
approach: ledger/codec body recognition, plan and trace reconstruction,
protocol current-state and End fact issuance, and associated diagnostics and
proof-only harnesses. Remove retained superseded code where its only consumer is
the old protocol checker; first map actual consumers and preserve generic N2
transport, resource, retained-control and host behavior. Do not delete evidence
or alter unrelated dirty work. Prior models and test receipts are historical:
reuse only the result and boundary they actually cover, with source equality
where needed.

At a frozen source and configuration, exercise the public native Work/Ack
fixture, Full and reverse-traffic progress, actual End and settlement, and
ordinary malformed input, unmatched/duplicate/wrong-peer Ack and operation
failures without early release. Exercise actual local cleanup, including the
producing-cleanup continuation, and outstanding host delivery/callback failures.
Run applicable existing generic static type, effect and retained-control
negatives separately. Test codec zero, boundary and large numbers, malformed
and truncated data, full consumption, and copied bytes through the actual
bridge. Verify imports and the ordinary production build path. No test-only
injected plan or private-only run substitutes for public acceptance.

Measure validation and execution separately for the actual small public
fixture in a supported release configuration; report Rust build time separately.
Record commands, source pins, machine and cold/warm conditions. Compare
validation with a similarly sized ordinary Ash program under the generic rules
and with the obsolete protocol-checker baseline. The aim is validation cost
comparable to the ordinary program and a major measured drop in wall time, work
and state from that obsolete baseline. Four-minute validation is unacceptable;
no minute-scale duration is accepted by default. Establish the concrete budget
from the generic baseline, not an invented ceiling. Do not raise work limits,
pad the source or exclude normal work to meet it. If the measured cost or a
required lifecycle fails, report the cause and return the gap to design; a
faster private diagnostic is not acceptance.

After focused checks, obtain independent review of the connected source and
receipts, run the required full workspace verification, and update the
specification only with implemented, reviewed behavior. Preserve separate
milestone and Main gates and record actual retention and acceptance.
