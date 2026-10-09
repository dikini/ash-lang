# Regression-only Arena disposition, 2026-10-09

The active source contract is verified baseline `f23ea77`: Common control,
SQLite String/TEXT copying and scalar Arena storage. This is an informative
experiment record, not semantic adoption. New features are deferred as recorded
in [Arena results](../arena-results.md#regression-only-scope-and-deferred-work-2026-10-09).

The [recovery commit](recovery-commit.json) and [92-file manifest](recovery-files.json)
preserve the unfinished candidate. [Round 22](round-22-receipts.json) and
[round 24](round-24-receipts.json) retain distinct failed-round results and their
complete source manifests. Raw logs remain in the ignored persistent recovery
path `.worktree/recovery/arena-completion-20261009`, outside the delivered source.
The recovery commit includes later unfinished edits and is not the exact source
of either test round; the manifests identify those tested sources separately.

[Independent review](independent-review.md) verifies scope, authority boundaries
and preservation. Fresh connected baseline and actual integration evidence are
recorded below. No new Main action or push is part of this work. The temporary task, plan and execution record are retained in recovery
Git history rather than restored to the active project-management tree.

## Fresh baseline verification

All commands ran against unchanged `f23ea77` executable source (401 Rust/Ash and
Cargo file hashes), with the six unrelated draft hashes unchanged. The
[connected receipt](baseline-receipt.json) records exact commands, exit status,
duration and raw-log hashes. [Source pins](baseline-source-pins.json) retain
the 401 tested Rust/Ash/Cargo files. No baseline bug was reproduced
and no production or test implementation change is delivered.

| Connected check | Observed outcome |
| --- | --- |
| Established public Arena/SQLite source, copying, sessions and control | 39 passed across six targets; no failures or ignored cases. |
| Existing stack and exact dictionary regressions | Five passed; original 64 KiB cases unchanged. |
| Adapter unit and native backing | 49 unit and ten backing cases passed; no failures or ignored cases. |
| Packaged hosts | Five SQLite programs and scalar Arena passed exact value/native/copy/completion checks. |

The [host receipt](packaged-host-receipt.json) retains actual values, SQLite types
and copy sizes, native events, phase costs and source/binary/output hashes.
Scalar Arena returns `Completed(41, Closed)` with Acquire → Store → Load → Release
for the same activation/object: eight actual bytes, one object, normal source
release and no host teardown. Its original host has no type/retained-owner report;
zero retained owners is checked by the public suite rather than inferred from
missing host output.

| Host | Source checking | Final elaboration | Independent Core |
| --- | ---: | ---: | ---: |
| sqlite-text-entry.ash | 164,084 | 60,696 | 91,011 |
| sqlite-copying-entry.ash | 1,213,287 | 166,073 | 903,995 |
| sqlite-session-entry.ash | 598,589 | 377,132 | 1,609,027 |
| sqlite-control-resume.ash | 203,627 | 103,926 | 289,063 |
| sqlite-control-discard.ash | 263,417 | 147,288 | 109,243 |
| arena-allocation-entry.ash | 88,793 | 27,096 | 82,277 |

Every completed phase fits its unchanged nominal budget: 1,245,184 source,
393,216 final and 1,638,400 Core units; the existing 10% hard allowance is
unchanged. These are charged work, not time or physical memory measurements.
Codec scratch, evaluator heap and allocator overhead remain unmeasured.

## Actual integration verification

Unsigned merge `7e754bd89b32acad2caa87620c7ea84af3c49e89`, tree
`a372685987f567c568978c82df2f0d5f82020600`, preserves integration parent
`f56070ccb88d21ba833c5ca70106070318b9145a` and documentation delivery
`09fdf41f4d66f4ec9dd492f7ef8ebfdd3bde2d5f`. The wider recovery commit is
excluded from this ancestry. Executable source remains the verified baseline.

The single `cargo xtask verify` in the actual `codex/provider-experiments`
checkout passed all six ordered stages: format, metadata, all-target build,
strict all-feature lint, workspace/all-target/all-feature tests and
warning-denied documentation. The [integration receipt](integration-receipt.json)
records exit 0, 1,434.08 seconds, unchanged 403 Rust/Ash/Cargo file hashes,
unchanged six draft hashes and unchanged tested HEAD. Outer Cargo summaries
record 3,475 passes, zero failures and one existing ignored calibration case
across 119 targets. Four targets execute no cases; nine nested child summaries
are excluded. The ignored case is
`generated_resource_sessions_close_every_connection`, which requires an
explicit generated calibration fixture and session count.

The [accounting and native-source review](integration-review.json) retains
capture environment, merge parents and a post-gate snapshot of the SQLite C
bridge/header. Both native files equal the tested commit and baseline. This
snapshot was captured after verification. The later documentation-only tracking
commit retains the same executable source and does not establish another full
gate. Main remains `f23ea77`; no new Main merge or push occurred. All 33 stashes
and the six unrelated drafts remain preserved.

Raw logs remain in the persistent ignored recovery directory; the integration
log SHA-256 is
`b854ee5397d65960162e31607d7b8dca6724b392040bad923c268d70c100b6c3`.
The retained runner scripts are the exact capture definitions for this checkout,
not a portable build tool; reproduction commands remain in the
[established delivery recipe](../main-delivery-2026-10-08/README.md#reproduce).
