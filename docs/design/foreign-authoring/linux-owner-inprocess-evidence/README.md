# Owner packaging observations and proposed map-only budget

Informative F2 experiment evidence for issue #58. This delivery proposes only the
[map budget amendment](../linux-owner-inprocess-experiment.md#prospective-map-only-budget-amendment).
It records selected-source compiler production, ordinary legacy owner-host
generation and two static-relink refusals. No static candidate has passed
inspection or started. No ownerful architecture, checked runtime, deployment,
store/context, isolation or whole F2 acceptance follows. AD-0015 stays owner-free.

## Inputs and correspondence

The selected compiler source is commit
`1a8ecef0b03ddc75a45254543bd8f6f0bb10969c`, tree
`e4ab5e35b50d64326e548fc54cf264a4af170832`. The
[complete selected manifest](../linux-owner-inprocess-probe/preparation/selected-archive-manifest.json)
pins all 2784 blobs (96,452,672 content bytes). Its 177-input build.rs runtime
census is separate. Each successful build phase verified complete snapshot and
its declared tool/configuration inputs before and after. The
[original contract bytes](stage1/experiment-contract.txt), SHA-256
`27430b69ee44dcbcb835a83dc38ff2b034826b81dddae40b7bb9ba7b4377cc3e`,
were retained by PR100 at `2ac8c393846715249de5a475a65e47bf1309bb54`.
The proposed new map budget does not rewrite that contract or the old assignments.

The [adapted owner](stage2/experiment/owner.ash) changes only the two native
symbol names to malloc/free; the [entry](stage2/experiment/entry.ash) requests one
eight-byte opaque allocation. Its read returns independent stored input 8;
it does not read native memory. This is the legacy direct-resource baseline,
not PR97's static checked lifecycle. No Borrow/current-window or C-to-S extension
is introduced. The generated [root source](stage2/generated/src/main.rs),
[Cargo manifest](stage2/generated/Cargo.toml),
[post-resolution lock](stage2/generated/Cargo.lock) and
[generated inventory](stage2/generated-manifest.json) retain actual associations.
The [initial lock seed](stage2/selected-Cargo.lock.seed) comes from selected-source
embedded-write correspondence; it was not independently captured as a generated
pre-Cargo file. Internal Cargo may resolve that seed before public build returns.

## Actual assigned results

| Phase | Actual result | Process observation |
| --- | --- | --- |
| Selected compiler | Success; 186.285883 seconds, 80,344 output bytes | Child 0; one reaped, no pending/escape/limits |
| Public owner generation | Success; 171.924367 seconds, 58 output bytes | Child 0; one reaped, no pending/escape/limits |
| Static relink, default map | Refused at 16 MiB map limit; 9.735813 seconds | Child -9; five reaped, no final pending or escape |
| Static relink, discarded diagnostics suppressed | Refused at 16 MiB map limit; 11.236444 seconds | Child -9; five reaped, no final pending or escape |

[Stage1's observed compiler](stage1/observed-compiler.json) binds actual normal
Cargo package/manifest/source artifact records with fresh=false, runtime
fingerprint, dep-info and build-output records. The compiler was 589,364,584 bytes,
SHA-256 `5dca1b624bf206c44c6c4d3037675193800516eb936a0cf6420e67394e998d3e`;
its runtime fingerprint was
`6ed612090a3fadfbcc982c0cf41b210cb02e2d01af7db5a5958e63a6fc527a47`.
This is historical selected-source evidence, not a promise that the shared-cache
compiler still has those bytes after other builds. No Borrow binary was reused
by intent or relabelled as selected-source output.

[Stage2's producer receipt](stage2/generation-receipt.json) binds seven generated
files and the ordinary host (475,650,552 bytes, SHA-256
`d5799c76fbf3be8b06a473906b4e73ce82b1fdf90db4a1b1923d958816fe0a61`).
The ordinary host is a build intermediate, not the final 128 MiB static candidate,
and was never executed. Generated native bridge text binds nullable opaque
Allocate to malloc(size_t) and State-only consuming Free to free(pointer), with
original owner/formal/source records. This is producer correspondence; actual
header/ABI checking, complete static native closure and runtime admission remain
unproved. The private payload and expected facts are omitted binary artifacts,
with exact observed digests in the inventory. They are not newly decoded or
executed by this delivery.

Both static attempts ran only the before-verifier and monitored relink.
After-verifier, candidate copy, readelf inspection and final receipt were not
run. See the original [first sequence](stage3-default/execution-readback.json)
and [second sequence](stage3-no-discarded/execution-readback.json), plus their
monitor receipts linked by the retention index. Each refusal recorded temporary
pending reaping during cleanup, then all five owned children reaped and no final
pending children. Those process facts do not prove source finish or native Free.
No artifact left in the shared target by a killed linker is admitted as a
candidate or subsequent successful output.

## Why the prospective map-only change

| Attempt | Observed map size at refusal | Exact retained prefix | Prefix content |
| --- | --- | --- | --- |
| Default | 17,346,560 bytes | [16 MiB prefix](maps/stage3-default.prefix) | Discarded sections starts at byte 519242; no active-map/LOAD/OUTPUT marker |
| No discarded diagnostics | 17,674,240 bytes | [16 MiB prefix](maps/stage3-no-discarded.prefix) | Active map at 519386 and LOAD at 519416; no OUTPUT marker |

These are sampled oversize observations, not complete-map sizes. Neither raw
oversize external map was fully hashed or declared complete. Each prefix hash
is a hash of exactly 16,777,216 retained bytes, not of the whole map. The
[diagnostic-option provenance](stage3-no-discarded/map-detail-evidence.json)
records the pinned installed BFD manual and its short relevant excerpt:
`--no-print-map-discarded` suppresses discarded/garbage-collected map listings.
That suppression worked, but the remaining active map still exceeded 16 MiB.
No option changes source, native bindings, ABI contracts or executable semantics.
The exact relink uses cc plus explicit `-fuse-ld=bfd`, not rustc's default LLD.

The proposed 64 MiB allowance applies only to a complete new map. Logs and
command output stay at 16 MiB; all other bounds and existing framing, LOAD and
pinned libc.a gates stay unchanged. The executed
[monitor](../linux-owner-inprocess-probe/build_monitor.py) has a shared watched-file
limit and cannot yet express that split. A future exact tuple needs independently
reviewed per-class enforcement/retention, fresh paths and source/tool checks.
Sampled observations can overshoot or miss intermediate changes; they are not
hard quotas or proof of an unobserved peak. This delivery changes no monitor,
collector or executed command. It does not assign another attempt.

## Retention and verification

The [retention index](retention-index.json) maps every original execution-inventory
record to its exact retained path or explicit omission. The four original
execution manifests are retained unchanged and may refer to omitted external
files; they are not inventories of this compact publication. Historical README
and contract bytes use `.txt` suffixes to distinguish original path-relative
records from the current documentation. Each map prefix is stored once, shared
by its original inventory and this index. The second prefix contains original
trailing spaces and neither prefix ends in a newline. Preserve those raw bytes;
whitespace checks on authored prose exclude exact captured records. This is an
evidence exception, not source formatting permission.

No compiler/host/private binary, cache, source archive, system header, full map
or obsolete preparation generation is copied. Missing original artifacts and
absolute /tmp paths limit reconstruction; a receipt/hash alone cannot recreate
them. Other shared-cache builds may replace historical outputs. The selected
archive and full source remain external, associated by the existing complete
manifest. New observations need a fresh reviewed assignment; copied records are
not newly executed results. Original producer receipts and both failures remain
unchanged. Dispose of external failed maps/generated roots only after independent
evidence review; preserve useful shared cache under the current sole operator.

The [publication manifest](manifest.json) binds this subtree and both informative
document changes. The staged verification checks copied-original equality,
manifest membership/hashes, UTF-8/JSON/Python syntax, relative links and read-only
patch application against the stated base. No Cargo, compiler, linker, readelf,
owner image, benign child or native probe is run during this documentation work.
The historical tuples/configs are evidence, not reproduction commands to execute.

Header/ABI correspondence, a complete inspected static candidate, native/runtime
loading and shutdown premises, ownerful architecture review and a fresh exact
startup approval remain pending. F4 O/K reservations/quarantine/completion, F6
immutable receipt/approval/store/context enforcement, checked runtime/image
activation, C-to-S/SQLite and F7 isolation/credentials/storage/filter/quota/fault/
termination evidence remain separate obligations. All whole-scope F2 criteria
remain open.
