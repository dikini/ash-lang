# Current v14 required image refresh

This draft checkpoint rebases PR110 onto retained PR117 commit
`4e995067edad3426f37bdd07f09a1efdc13674e6`. All nine prior commits have equal
range-diff entries; `codex/pr110-before-v14-602b` preserves the previous head.
The new source adds only an empty `decoded_rows` map to a retained provenance
test's Decoder initializer and an optional bounded test-only evidence hook.
The hook retains original encoded bytes and expectations before decode/restore,
with exact selector, ordinal and length association. Ordinary tests leave it
disabled. Product work meters, default allowance 327680 and required selectors
are unchanged. No foreign callee or generated executable ran.

Both required tests were observed independently on fresh current-codec inputs
and remain red. Session 78381 selected the Row test: base-image exact/prefix/
short/spent/fresh and hostile controls completed at work 247604; the subsequent
full-Row canonical restore returned `Validation(Resource)`. Session 25358 then
selected only Access directly on the same pinned libtest, without rebuilding or
repeating Row. It reached its static helper/independent-Core refusals, then the
canonical image returned `CoreAdmission(TypeWorkExceeded)`. Later required-image
bounds/hostiles receive no credit. Current failures do not identify their paid
caller, complete demand or a required saving. Historical v13 totals, callers and
process variation do not transfer to these v14 inputs.

<!-- markdownlint-disable MD013 -->

| Case and ordinal | Image bytes / SHA-256 | Expectations bytes / SHA-256 |
| --- | --- | --- |
| Row base 0 | 32356 / `fe226cf21f77bcb22b1115ecfb8d8f31102e3bde79701dd205b179b4bd323a8a` | 21105 / `940384e60e5ac9b52fee01338b563cfa30e5061dd4e9d3fbd9554c17f6fc3b09` |
| Full Row 1 | 34856 / `3a429973c33216c6607244ac90d8ddb51d2e7edcb87e7e904054d27a0e5dadc9` | 23454 / `a68f8c553abac9525b0c6240a86fc60c653356277948b3eff06086a7c5133ad0` |
| Access 0 | 43574 / `4f6c4b1aeeaa6fca6069a0f4e2c8d7f700c88111c1597ffc98e271e67969c1e1` | 28479 / `1a6a97c04a78f4f3d0799e81a13f4388d8a6a3766b50d1db60cf61febb2dacd1` |

<!-- markdownlint-enable MD013 -->

The 7060 full / 623 runtime before-and-after input maps match for the actual
selected runs. The shared artifact is SHA-256
`6d3d795e0d9a2ad3cff2f2224bf3810795e1fa2c2f4138ec5d10567828733068`,
607331776 bytes. Source/tool pins and capture associations were independently
audited; children were reaped and groups absent, with no resource-watcher abort.
These are independent test processes, not repeated operations on one fixed wire.
No Clippy, startup refresh or general process-order stability result is claimed.

The original 78381 controller receipt remains `valid=false`: its announcement
regex missed the first message after Rust's `test NAME ...` prefix. It stopped
before Access. A separate later observation and independent audit qualify the
actual Row raw result and both complete capture triplets; the original receipt
is neither rewritten nor relabeled green. The corrected Access-only operator
accepts exactly that optional escaped selector prefix and requires complete
triplets, metadata, actual artifact and setup-failure discrimination. Earlier
session 17430 is compile-only E0063 with zero selection/captures: it exposed the
missing test initializer field. Access was unrun in that attempt. Proposal 01
was unrun; it is not imported as dynamic evidence.

[index.json](index.json) reconstructs 55 originals and four map variants from
52 deterministic gzip blobs, totaling 527456 compressed bytes. These include
the exact current wires/expectations, operators, raw logs, receipts, separate
posthoc Row qualification, independent audits and tested source snapshots.
[verify.py](verify.py) checks all reconstructed hashes and available originals.
No executable/cache is imported. Task/evidence additions are post-test prose;
they do not manufacture a uniformly tested new full-input map.

Next: review a narrow current-input causal observation before another product
repair. Preserve fresh authority checks and unchanged defaults. Required-image
success, remaining controls, specification delta, regressions, startups, Clippy
and final review remain open. PR110 stays draft; whole F3, F-core and Main stay
open. Eligible dependency-free F4 preparation keeps its own closure and
implementation/execution prerequisites, without waiting for whole-F3 closure.
