# TASK-0058: Pinned worker network

- ID: `TASK-0058`
- Status: active
- Related: [specification](../../spec/README.md), [AD-0017](../decisions/AD-0017-pinned-worker-host-and-transport.md), [DN-0058](../design/DN-0058-pinned-worker-host-and-channel.md), [M4 issue #55](https://github.com/dikini/ash-lang/issues/55)

> This task organizes work. It does not define Ash semantics.

## Dependencies

M1–M3 are complete on Main at `67c79ddc32a813cc0c9ddab2962f9e2aa849b028`;
their acceptance is recorded in [#51](https://github.com/dikini/ash-lang/issues/51).
N1 contract and host/channel choice were independently reviewed at
`b296e17ce9e4f1760ce73df4f4716ef0c0fb2093`. AD-0017 records the
current host choice. The
[focused execution plan](plans/pinned-worker-ordinary-protocol.md) sequences
the revised ordinary Ash protocol delivery. The earlier
[execution plan](plans/pinned-worker-network.md) records the superseded checker
approach and is historical for N4/N5; it does not authorize that approach.
On 2026-10-31 the user directed ordinary Ash protocol code and ordinary error
handling, without compiler protocol reconstruction or a new runtime checking
framework. AD-0017 records the host decision and the milestone specification
records the implemented language boundary, including the codec's integer
module. The
previous N3 review and proof establish only their recorded historical scope,
not a prerequisite checker gate or a completed ordinary protocol. Main
integration remains a separate gate.

## Current delivery status

The live [M4 ledger](https://github.com/dikini/ash-lang/issues/55) records
milestone inputs and outstanding gates. The ordinary Work/Ack and producing
cleanup implementation, tests, specification, review and fresh seven-stage
gate were retained on the milestone in [PR #187](https://github.com/dikini/ash-lang/pull/187)
at `45676a607ac7565cc4c9f9cc926dd3dbe274baa1`. N6 and Main integration remain
separate. Historical checker receipts do not establish the revised program's
guarantees. The source-order limitation discussed in earlier evidence remains
a generic validator issue; source ordering is not a language requirement.

## Work

The ordinary Work/Ack/drain and producing-cleanup slice is retained on the
milestone. Complete the cross-milestone program, remaining verification and
Main delivery. Preserve
original user-visible outcomes from [#76](https://github.com/dikini/ash-lang/issues/76)
through [#81](https://github.com/dikini/ash-lang/issues/81), applying the
revised direction to superseded checker-specific implementation criteria. The
focused plan names the connected acceptance path, negative cases, removal work
and performance measurement. Complete generic and native gates, independent
review, the specification update and full verification before final delivery.
Partial slices do not close a whole criterion.

## Historical progress

The following entries record the decisions and status at those checkpoints.
Earlier requirements to finish the protocol checker are superseded by the
2026-10-31 revision above; no historical entry claims revised acceptance.

The N1 source/Core contract and host/channel choice are accepted and retained
through [PR #168](https://github.com/dikini/ash-lang/pull/168) at
`993be1e7c932d1db20e62a706df5dab26698fa99` on the M4 milestone branch.
Independent current-head review covered all nine artifact/index files and 164
local links and anchors. The retained tree equals the reviewed head; local and
origin milestone refs match. Author acceptance was applied and read back, and
[#76](https://github.com/dikini/ash-lang/issues/76) is closed. This accepts the
N1 contract only; later contract refinements need their own dependent delivery.
N-core, N-proof and N-final gates remain pending.
The developer owns acceptance notes after retention; the orchestrator assigns
each next checkpoint and integration action. N3 contract acceptance is
retained through [PR #169](https://github.com/dikini/ash-lang/pull/169) at
`6cd6873e175d9453e734f3e8a0b0c0ce98482d6e`, with author partial acceptance
applied and read back. This does not claim the full proof, checker or issue
acceptance.
The unconnected N3 ledger checker is temporarily test-only at the N-core
boundary. Its conditional witnesses remain available to tests; N3 must restore
the production module and connect the actual validator callback before claiming
currentness. The N3 proof and N4 codec, composition and release obligations
remain open.
The bounded N2 worker/channel source proof gate passed on the reviewed
`eecc85178641f4eaf41cae696653e80003c24432` closure; its
[evidence](evidence/pinned-worker-channel-proof/README.md) records its limits.
The reviewed proof prerequisite is retained through
[PR #170](https://github.com/dikini/ash-lang/pull/170) at
`fc613e4a`; author partial acceptance was applied and read back on the related
issues. The same-carrier terminal-failure retention clarification is retained
through [PR #171](https://github.com/dikini/ash-lang/pull/171) at
`aae400047073d4078f544b77546871dda6261fe8`, with author partial acceptance
applied and read back. Neither prerequisite retains the runtime candidate or
completes N2 acceptance. The accepted one-way contract refinement is retained
through [PR #172](https://github.com/dikini/ash-lang/pull/172) at
`f7f5994f2ec013fa2a67c118b882f6342e3a4dab`, with author partial acceptance
applied and read back. Full N2 runtime acceptance remains pending.
The revised one-way modeled execution proof at source SHA-256
`870b4f0f4b134e49a2d97a1039d8f362700cb2ff1f7d667877d6cb9816e1573c`
passed the independently audited frozen source gate: evidence SHA-256
`f9856027f5a6828cb19bac639a79291fd1a4c6d6cfc538f11b54ed2194208dd2`.
OneWayCompletion compiled freshly; four parent modules reused validated
receipts, with 283 ordered standard-axiom reports overall. The exact model,
full five-module registration and text evidence are retained through
[PR #173](https://github.com/dikini/ash-lang/pull/173) at
`b228277316025c37bf2b2da01ad412147729cad1`. Independent review cleared
head `e2ca2fcf`; the retained whole tree equals that reviewed tree, milestone
refs are synchronized, and author partial acceptance was applied/read back
on N2 and its parent. This proves modeled source obligations only.
Actual linked Core and C3 correspondence, native/runtime refinement,
cumulative budget coverage, imported-helper correspondence, N-core and
full N2 acceptance remain separate obligations. Code delivery continues
in parallel with proof packaging.

The static Message-to-root route, processing-cut issuer and runtime consumer
passed independent review at the frozen `ash-integrated-cut13` receipt,
manifest `01a1072d6cf8c47c2d7230d99132669a110f1a5b54c30d1cd7ee56b01c0ca002`.
Actual linked validation records the route and matching cut provisionally;
the no-finish variant records neither. Required cut negatives and Network
handle/acquisition-type scope checks pass. This conditional cut covers the
supported helper/native return, message escape and saved suffix fragment;
it is not public completion or a full N2 gate.

The subsequent all-owner C3 handoff passed independent code review and the
corrected four-case validator test at manifest
`1abe1c4be161a9d1ef79aafa4695c8b67f18fc88f088dd1e5e37abd96d924dfa`.
At that checkpoint the requested positive reached the Network lifecycle
`Registry` gate; no-finish, failed baseline and unrelated Unit-root Store cases
retained `RetainedRelease`.

Both actual worker End descriptors now pass the integrated validator test,
using 120,488,904 cumulative work units within the unchanged source-derived
allowance. The End query reuses existing C3 selected-clause and restoration
semantics rather than requiring unique caller-stack addresses through recursion.
The canonical finish-wrapper authentication already excludes an intervening
boundary inside that wrapper; the earlier review request for a synthetic
in-wrapper boundary test was withdrawn. The same-binary intervening-receive, constructed-End and altered-Boolean
negatives refuse; the Store-boundary case refuses earlier at focused C3. Inputs
match before and after testing, with Rust manifest
`5b5f7c7fbfd1662cef31810ecb3ffcc8c42e8d771e4e02093088e00675de2896`
and receipts in `/tmp/ash-end27/`.

The public copied-byte integration now passes linked validation and execution,
including actual Message processing and settlement. Session `24128` passed 1/1;
the receipt is `/tmp/ash-restored-tuple2/public.log`. On the same frozen inputs,
the focused query recorded 13 Store foci and 13 empty exits, an authenticated
End route and a processing cut; receipt `/tmp/ash-restored-tuple2/focus.log`.
The 64 KiB ordinary-analysis stack regression passed in
`/tmp/ash-restored-tuple2/stack.log`. The source/config manifests matched at
SHA-256 `9cfdcad9724e2781b49fb9ca5de40119eea0e36b1dde0c9d681d1047433fc62a`.
On the same library binary, the native one-way cases passed 3/3; tainted
recursive carry, message escape, pre-tail message use, intervening receive and
finish-boundary controls passed. Their receipts are in `/tmp/ash-restored-tuple2/`.
These results do not complete the remaining N-core and N2 gates.

The connected, unretained candidate subsequently passed the actual linked
one-way native fixture: both workers completed and joined, the owner settled,
the program returned `42`, and the native callback was observed once in main
and once for the received Message. Session `65316` passed 1/1 with matching
source manifests at SHA-256
`95a71f8927899cfe4f7c337849b092d7df23cb82228d682ffc5ddb14927c76ff`;
the local receipt is `/tmp/ash-native-oneway2/`. An independent review cleared
the connected runtime code boundary, subject to the remaining evidence and
retention gates. The candidate has not completed N2 acceptance.

Required N2 evidence still to reconcile against the existing receipts:

- The linked native fixture also passed with two Messages and recursive frames,
  observing Empty before the first and between deliveries. Separate native
  Signal callbacks coordinated the test; EchoBytes counted actual Message
  processing. Session `36285` passed both the original and coordinated cases
  (2/2) with matching source manifest SHA-256
  `c601f05a1ca6d4c71bebc55195abc721c9f8e767187e739e4268bfb873af2c49`;
  the receipt is `/tmp/ash-multi-empty/cargo.log`. The linked no-return-base
  control refused with Resource and produced no completion fact at 162,250,000
  work units; it did not converge to a trace. The model's `no_base_no_returns`
  theorem provides the separate modeled result. Session `88771` passed that
  conservative control; receipt `/tmp/ash-ncore-failures/no-base.log`.
- Map the linked-Core refusal evidence for unsafe suffixes, escapes, pending
  cleanup or C3 work, forged or stale End, wrong activation or side, intercepted
  operations, changed targets/evidence/imports/transforms and budget exhaustion.
  Check receive, marker and callback failures separately. The linked failed-send
  control selected `SendFailed` and a refused finish and could not settle:
  session `92244` passed 1/1 with source manifest
  `b632e58e78c05c5d1d751edeccb2acac1ba0600c5589d2167a43e15db9683702`;
  receipt `/tmp/ash-ncore-failures/send.log`. An actual checked native callback failure during Message processing passed 1/1 in
  session `88371`: the same held delivery remained in the carrier and its
  failure report, and normal settlement failed. Source manifests matched at
  `8a5537392e4277b8126b318e4ccf6377c7511406f51f729c00fcb77e01d0e122`;
  the receipt is `/tmp/ash-native-failure2/cargo.log`. The existing actual
  source callback/captured-cell regression also passed its injected
  work-exhaustion and disposal checks in session `46419` (1/1), with source
  manifest `8b38ed4d93a34f458e350ca9cfe2132bf2e29aacfe4bbb0149b95035980dbbac`;
  its receipt is `/tmp/ash-pure-linked/callback.log`. This covers ordinary
  callback behavior outside the Network path.
- The transport and worker regressions passed 16/16 and 18/18 at manifest
  `6c1cbdd319653f5a13a5fbcca612ee2ba0ceb85eba00301189dbfb5261c09f9b`;
  receipts are `/tmp/ash-connected-runtime/cargo.log` and `worker.log`. Within
  that snapshot:
  - `bounded_fifo_copy_and_end` covers capacity-one Full, FIFO and copied
    bytes, restored receive head, genuine End and Closed. `reservations_keep_fifo_and_block_settlement`
    covers accepted pending work and `terminal_failure_preserves_reserved_delivery`
    covers terminal receive failure before commit with refused settlement.
  - `peer_publish_and_cancel_are_serialized`,
    `pending_wake_survives_readiness_reversal_and_stale_tokens_are_rejected`,
    and `late_watch_rechecks_both_directions_and_users` cover the tested race,
    stale hint and both directions. `settlement_needs_drained_channels_and_cancelled_watches`,
    `pending_send_blocks_seal_and_settlement` and the three receive/send guard
    backing tests cover the exercised outstanding registrations and users.
  - `worker_marker_return_preserves_owner_on_budget_failure` covers both marker
    charge failures; `worker_end_observation_requires_host_end_and_successful_reply`,
    `worker_end_reply_allocation_failure_does_not_publish_observation` and
    `worker_newer_receive_invalidates_pending_end_including_overflow` cover
    the tested End identity and stale-result cases. `worker_failure_preserves_committed_receive_obligations`
    covers an unhandled failure after receive commit; the native callback
    failure and failed send have the separate receipts above.
  - The failed-send control covers failure before send commit;
    `terminal_failure_preserves_reserved_delivery` covers failure after send
    commit and before receive commit. `worker_failure_preserves_committed_receive_obligations`
    and the separate native-failure receipt cover failure after receive commit.
    The selected host Region provider's Message-copy allocation failed under an
    injected work limit in `worker_selected_provider_message_copy_failure_restores_fifo_head`:
    the held reservation remained and its original FIFO head was restored.
    Session `57394` compiled and the direct test passed 1/1 with matching
    manifest `1631acbc80277daa8a8e9fc68aec27190a8a7c4129164b62ec22c623e446187f`;
    receipt `/tmp/ash-provider-feedback/provider.log`. This does not establish
    behavior of arbitrary custom providers. `worker_capacity_one_feedback_allows_producing_cleanup`
    exercised two worker interpreters exchanging an initial message and reverse
    acknowledgement before the producer's actual cleanup sent a second message.
    It passed 1/1 from session `75526` with matching source/config manifest
    `5661a9d5d1a5f2c4f6b0dbad43c62923e895fcca8efaf035df6664b7b4551b73`;
    receipt `/tmp/ash-feedback-cleanup/feedback.log`. Its worker-local returns
    did not authorize settlement; it is not a bidirectional owner-settlement
    result.
- Complete and review the actual Core/C1/C3, runtime, native, imported-helper
  and cumulative-budget correspondence against the modeled results above; freeze
  and independently review the N2 and N-core evidence, retain the delivery, and
  run the required workspace gates.

At the historical checkpoint, formal evidence covered the then-required model laws. The Rust-to-model mapping and
ordinary runtime/primitive correspondence are trusted boundaries checked by
independent review and required tests; this task does not formally verify Rust.
Those historical protocol-checker obligations were superseded by the 2026-10-31 direction.

## Verification

For N1 check artifact authority, relevant links and cases, independently
review adoption bookkeeping and verify the retained result. For
product slices freeze source/configuration inputs, run the required focused
positive, negative, generic C3, regression and native checks, obtain independent
review and verify actual retained commits. Retained generic proof evidence keeps
its original scope; historical protocol-checker models are not new gates. Run
fresh full workspace gates at the plan's checkpoints and before Main, reusing a
receipt only under its documented equality conditions. Use one Cargo job and
the compatible shared cache under the project workflow.

## Discoveries

Copying finite bytes removes the need for a general object-graph transfer in
N1. It does not authenticate a completion message, prove native visibility,
or discharge local retained-control completion. The live N6 issue requires
SQLite coverage and a gap assessment at the ordinary byte/pointer FFI boundary;
historical checked or isolated FFI modes are not prerequisites.
The N6 SQLite canary is the existing
[`direct_sqlite_getters_return_nonnull_repeatable_addresses`](../../tests/program_build_native.rs)
program-build test. Its declarations call `sqlite3_libversion` and
`sqlite3_sourceid` as `Unit -> Address` and compare nonnull, repeatable pointer
values; it does not read the returned strings or establish a full SQLite
binding. The existing linked native EchoBytes fixture covers a synchronous
`Bytes` argument separately. Open/prepare and ordinary result retrieval still
need numeric C slots, output pointers and foreign-memory readback or byte
results, which are not supported by the current FFI surface. The SQLite canary,
connected cross-milestone example and full verification remain separate
acceptance evidence; their presence here is not a fresh pass claim.

The analysis limitations in [#165](https://github.com/dikini/ash-lang/issues/165)
remain visible; this task neither adds a language restriction nor weakens the
existing checks to work around them.

## Deviations

On 2026-10-31 the user superseded the protocol-specific compiler checker and
then ruled out new runtime checking machinery beyond ordinary error handling.
The milestone specification and accepted decisions govern retained behavior;
evidence keeps its original scope. Return a missing language, bridge or lifecycle
contract to design and a proposal before implementation.
