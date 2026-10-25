# Trusted legacy owner diagnostic evidence

The one explicitly approved host diagnostic returned `Completed(8, Closed)`
plus newline, exited zero and was reaped. Its exact sealed image, receipt,
policy, premise and before/after pins matched. This observes the fixed legacy
owner baseline under explicit native/runtime/loading/host-loss assumptions.
It does not select ownerful architecture, prove native free or memory reads,
exclude runtime loading or implement checked runtime O/K/groups.

The [governing experiment](../linux-owner-inprocess-experiment.md),
[static packaging](../linux-owner-static-packaging-evidence/README.md) and
[header/closure evidence](../linux-owner-header-closure-evidence/README.md)
retain their separate claims. [AD-0015](https://github.com/dikini/ash-lang/blob/2766e8260e2590d9ebdca7abd699115b3cd02a8a/docs/decisions/AD-0015-linux-scalar-inprocess-whole-images.md)
remains owner-free scalar only. No decision or current Main semantic change
is created by this evidence. All four whole-scope issue #58 boxes remain unchecked.

## Actual sequence

[Chronology](chronology.json) distinguishes every gate and outcome.

1. Independently reviewed preparation and exact root approval bound the image,
   receipt, proposed premise, harness/policy, purpose/context/mode and bounds.
2. The separately assigned sandbox run refused setup/exec with errno 13; child 125
   was reaped and harness 78 retained no owner result.
3. Automatic host tool approval initially rejected execution for lack of trusted
   human approval for that exact out-of-sandbox launch. No wrapper ran.
4. After the human answered “Approve one host run”, normal tool escalation
   started the operator, but a Path/string error stopped it before Popen.
5. The failed operator remained preserved; a narrow reviewed repair, two benign
   tests and a no-spawn precheck passed. The human also stated “the followup
   native runs are approved”. No artifact/policy/security change followed.
6. The freshly assigned repaired operator ran the one host diagnostic through
   normal tool approval. The exact 21-byte report was observed and cleanup passed.

Human quotations here are explicit root-relayed parent-chat readbacks, not
a fabricated raw chat transcript or a product authentication mechanism. The
[root approval](actual/root-approval.json) is exact historical experimental
authority; it cannot be replayed as a protected F6 approval store or new command.
The [sandbox](actual/actual-handoff.json), [tool rejection](actual/host-tool-approval-rejection.json),
[pre-spawn failure](actual/host-launcher-setup-failure.json) and
[successful host result](actual/host-actual-handoff.json) remain distinct.

## Observed bounds and correspondence

The static image is 71,022,184 bytes, SHA-256
`52f09983205ecb2b524a3572fba267e79e28057c933f6408f7fde0f3ac42bc65`.
The [policy](actual/policy.json) caps image 128 MiB / PH 64, receipt 256 KiB, approval 64 KiB,
combined output 16 KiB and child termination-request deadline 30 seconds.
The harness copies to executable memfd flags 19 / mode 0500, seals write/growth/
shrink/seal changes, then hashes/inspects the final immutable fd and matches
approval. Fixed argv0/empty environment and standard descriptors are selected;
unrelated child FDs close before executing that same fd. No pathname reopen
selects executable bytes. The private copied pathname is tampered after pinning
and changed-path admission refuses; no old executable replacement was used.

[Host execution](actual/host-execution.json) and [case lifecycle](actual/case-w3hn5tw1/lifecycle.json)
record child 0, reaped in 0.07195 seconds, no harness failure and exact 21-byte
`Completed(8, Closed)\n` output. Six no-child approval/receipt/image negatives
and three EPERM sealed write/grow/shrink attempts passed. The temporary copied
candidate was removed; only case result/lifecycle remain. All eight artifact
pins plus Python matched before/after, and every sandbox record, prior rejection
and setup failure stayed unchanged.

[Source-derived rendering](preparation/expected-rendering.json) distinguishes
acquired completion from possible `NotAcquired(())` nullable refusal, which was
not observed and would not be the intended acquired-path positive. Entry asks
for size 8 and reads stored source data 8. No native memory-read callback exists
in this image. A printed report and process reaping do not independently prove
destructor internals/native truth, source completion on faults, checked K,
group reservation, quarantine correctness or no-loading behavior.

[Safe controls](preparation/safe-receipt.json) retain 14 passing methods. Fork/exec
are globally prohibited and mocked in lifecycle/reaping tests; the real seal
control uses synthetic 120-byte ELF-shaped data, never an executable candidate.
These test the harness state machine, not a second real owner termination.
The actual sandbox and host outcomes supply their own reaping observations.

## Retention and remaining obligations

[Retention index](retention-index.json) maps all exact original records, launchers,
repair and explicit external omissions. Original approval/status/absolute paths
remain unchanged. The image, full maps, compiler/cache and system/runtime/native
inputs stay external with exact digests or earlier retained manifests; no large
artifacts are copied here. Ten missing linker temporaries and distribution/
precompiled-runtime provenance remain qualifications. Repository-only replay
is limited by external bytes and would require a new exact assignment.

The manual trusted operator context promises no namespace/credential/group/
address-space/syscall/storage containment. Kernel waits may delay reaping;
30 seconds bounds termination request, not guaranteed kernel reclamation.
Root accepted residual allocator/ABI/lifetime/loading/error/unwind/shutdown/
host-loss premises for this bounded experiment as assumptions, not formal proof.
Faulty native code can corrupt or terminate the host, and host loss can prevent
any destructor or report. No privileged provisioning or security policy changed.

A separate proposed ownerful architecture/applicability decision must distinguish
this legacy diagnostic from future exact checked receipts and approvals. F4
reservation/guard/quarantine/copy/completion accounting, F6 immutable receipt/
admission/protected store/context enforcement, F7 trusted credentials/isolation/
fault/termination/quota evidence, C-to-S dependencies, bytes/windows, SQLite and
the full FFI milestone remain open. This delivery authorizes no further run.
