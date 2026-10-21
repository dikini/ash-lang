# Separately approved trusted scalar diagnostic

This addendum follows the [packaging inspection](README.md). The original
[producer receipt](producer-receipt.json) remains byte for byte unchanged at
SHA256 `4de5fe79b42c88fd3dc269a1438a0d5c24f190f199021c76ea3337178ff77d4c`.
Its no-execution statement describes packaging, before this distinct diagnostic.

## Authority and bounds

Root approved the exact reviewed image, receipt, harness, policy and inert
pathname replacement under the user's delegated recommended-choice authority.
The [actual approval](diagnostic/root-approval.json) is separate from the
[unauthorized template](diagnostic/approval-template.json). It accepts known libc
localization/gconv runtime-loading uncertainty and host authority only as
trusted diagnostic premises. No protected approval store is implemented.

The [versioned policy](diagnostic/policy.json) bounds image admission at 96 MiB,
control documents at 256 KiB, ELF program headers at 64, combined output at
16 KiB and the child deadline at 30 seconds. This is a new diagnostic policy;
the old reporter's 1 MiB bound/approval remain unchanged. The child uses fixed
argv[0], no additional arguments, an empty environment and sealed-fd execution.
The [approved harness](diagnostic/diagnostic.py) verifies create flags 19,
mode 0500 and all four seals (mask 15), rehashes before child creation and closes
unneeded descriptors. A deadline requests termination; kernel delays can defer
reaping, and launcher death cannot guarantee cleanup. Success requires observed
reaping. This trusted fixture has no authored descendant creation or fault
injection; these observations establish no hostile-code containment.

## Observations

The [host observation](diagnostic/host-observation.json) records `Returned(7)\n`
(12 bytes), exit 0 and observed child reaping. The candidate pathname held the
previously approved inert reporter B while the executed sealed descriptor still
held the exact generated evaluator/`abs` image A. The harness never executes B.
The host run used normal tool escalation for these exact approved artifacts.

The [filesystem-sandbox observation](diagnostic/sandbox-observation.json) retains
exec refusal EACCES (errno 13), child exit 125 and observed reaping; the harness
returns refusal status 78. This is not an isolation success or host-policy change.

Both runs retain seven pre-fork refusals (missing/altered approval, unsupported
or changed receipt, changed image and replacement before pinning) and three real
sealed-object write/shrink/grow failures with EPERM. The replacement-before-pin
case rejects a size mismatch; it is not evidence of a same-size replacement
comparison. Private executable candidates were removed after observed reaping.

The [execution readback](diagnostic/execution-readback.json), SHA256
`0fca855de2b1b1a3f96c6d66539a995e13dbf78714376e2a659ad9a68efeb752`,
pins the exact approval, observations and per-run result/lifecycle records.
The [preparation manifest](diagnostic/manifest.json) binds the approved harness,
policy, original prepared README/template and nine mocked tests. Those historical
files still say prepared/not executed because they precede the actual approval;
this addendum and readback provide the later chronology.

## Reproduction and limits

The retained [nine-test source](diagnostic/test_diagnostic.py) and
[original output](diagnostic/unit-tests.log) mock fork/kill/waitpid and fd exec.
Deadline, output-overflow and post-fork-failure cleanup are mocked controls only,
not actual generated-image fault observations. The tests' original receipt path
is the frozen local `/tmp/ash-generated-scalar.d771qtm9/producer-receipt.json`;
this is an exact historical harness, not a silently adapted portable runner.
The [reproduction receipt](diagnostic/reproduction.json) records a fresh run of
only these mocked controls, with unchanged source/policy/receipt inputs. No image
rerun accompanies this PR. Fresh execution would require fresh exact approval,
normal tool authorization and available pinned artifacts; retained approval is
not blanket authorization for another candidate or policy.

This demonstrates trusted existing-profile generated evaluator/bridge execution
from the approved descriptor under explicit possible-loading and host-trust
premises. **The strict no-runtime-loading requirement remains unmet.** No AD,
whole F2, product checked runtime, protected approval store, SQLite, isolation,
F4/F6 deployment or full-workspace/F-core acceptance follows from this result.
