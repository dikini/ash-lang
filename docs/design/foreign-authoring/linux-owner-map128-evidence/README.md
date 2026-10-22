# Full-map scaling evidence and proposed 128 MiB map budget

Informative F2 evidence for issue #58. The
[parent contract amendment](../linux-owner-inprocess-experiment.md#prospective-map-only-budget-amendment)
is proposed, not a command assignment. It keeps logs/output at 16 MiB, final
image at 128 MiB and complete-map/native correspondence gates unchanged. No
monitor, collector, tuple, build, startup or ownerful architecture is activated.
Accepted [AD-0015](../../../decisions/AD-0015-linux-scalar-inprocess-whole-images.md)
stays owner-free; [CP-0024](../../../proposals/CP-0024-checked-foreign-host-profile.md)
continues to govern checked semantics. Whole F2 remains open.

## Actual later refusals

PR102 retained the earlier compiler/generation evidence, two 16 MiB map refusals
and the 64 MiB map-only policy at 88db679943c981458b829e1c430e9af290976d9f.
The [prior evidence](../linux-owner-inprocess-evidence/README.md) remains unchanged.
Both next relinks used that historical 64 MiB cap; this new proposal does not
retroactively widen them or turn either into success.

| Attempt | Actual result | Map observation | Process cleanup |
| --- | --- | --- | --- |
| Third, per-class 64 | Limit refusal; 10.8906225 seconds, 59,047 output bytes | 68,108,288 bytes sampled | Child -9, all 5 reaped; no final pending/escape |
| Fourth, additional no-demangle | Limit refusal; 8.520340954 seconds, 59,079 output bytes | 70,373,376 bytes sampled | Child -9, all 5 reaped; no final pending/escape |

The exact [third inventory](third/execution-manifest.json) and
[fourth inventory](fourth/execution-manifest.json), sequence readbacks and monitor
receipts are copied without modification. Each ran only before-verifier 0 then
monitored relink 1; after-verifier, candidate copy, readelf and finalizer did not
run. Temporary pending reaping was observed during cleanup, followed by all five
owned children reaped. These facts prove neither native Free nor source finish.
There is no after-source equality claim, inspected candidate or full-map hash.
Sampled oversize files can be incomplete at different progress: their sizes
cannot rank complete map sizes or establish representation effectiveness alone.

Original contract 7e81587b and failed tuples still name the historical 64 MiB
policy and original paths. The [current 64 monitor](monitor64/build_monitor.py),
[tests](monitor64/test_monitor.py), [schema](monitor64/schema2.json) and
[fresh benign-suite proof](monitor64/reviewed-suite/suite-receipt.json) retain the
executed bytes: 21 methods/36 receipt cases, isolated outer environment,
source/interpreter pins equal before/after, and observed reaping/disposal.
Reduced synthetic test caps do not predict real map fit. Monitor64 remains
unchanged and cannot authorize 128 MiB via a self-test override.

## Why propose a finite 128 MiB map allowance

The [bounded postmortem](postmortem/prefix-analysis.json) and
[complete producer-metadata study](study/analysis.json) retain their original
source/data/provenance. The fourth prefix is still inside planned .text with
no OUTPUT marker; its 71,503 paired raw section/symbol names have identical
20,855,593-byte totals. Mangled rendering worked, but repeated names plus object
paths/addresses/extents/fill still consume 64 MiB. A .rodata substring belongs to
a .rela.rodata input pattern, not an observed .rodata output-section header.
No full map size or completed-link fraction is inferred from a prefix address.

The fixed ordinary producer 475,650,552/d5799c76 was fully hashed before/after
bounded Python metadata reads with unchanged file identity. It has 43 sections,
131,160 symbols and 27,704,553 referenced-name bytes. It is ordinary ET_DYN with
unstripped DWARF, not the final static candidate. Mutable cache-file contents
were not read or copied. Header/ABI and native implementation truth are not
proved by ELF metadata.

The [explicit model and recommendation](study/recommendation.json) combine
355.197 observed nonpaired-name bytes per pair with all ordinary symbol rows,
plus two name occurrences. The result is 101,996,794 bytes (97.27 MiB). A prospective
128 MiB map cap provides about 31.6% headroom above that model. It is an estimate,
not an upper bound or success guarantee; static CRT, grouping/order and unseen
nontext detail can differ. Keep every remaining active symbol/address/archive
record, existing diagnostic suppression/rendering, full-map hash, recognized
GNU/BFD framing/OUTPUT, nonempty LOAD and exact pinned libc.a gates. Missing
linker temporaries remain explicit producer/build-trust limits. The alternative
is a blocked packaging gate, not a partial-map or narrower-closure substitute.

## Exact prefix content in derived containers

Only the two exact retained 64 MiB prefixes use derived encoding:

| Prefix | Deterministic gzip bytes | Decoded bytes |
| --- | ---: | ---: |
| [Third](maps/third-prefix64MiB.gz) | 2,253,271 | 67,108,864 |
| [Fourth](maps/fourth-prefix64MiB.gz) | 2,058,994 | 67,108,864 |

[prefix-containers.json](prefix-containers.json) binds full compressed and decoded
SHA-256 values, sizes and original source paths. Compression used empty filename,
mtime 0, level 9/zlib 1.3.1; a second streaming recompression into a hash sink matched.
Container bytes are not byte-identical raw originals. Each decoded stream equals
exactly a bounded prefix, never the full oversize map. No raw 134 MiB duplicate,
full map, compiler/host/private binary, cache, source archive or system header
is included. Original files remain unchanged at their external /tmp paths.

[verify_prefix_archives.py](verify_prefix_archives.py) checks compressed size/hash
and canonical header, limits compressed input to its pinned window, and decodes
at most 64 MiB plus an oversize sentinel while hashing in 64 KiB chunks. It writes
no decoded output. The [equivalence command](equivalence-command.json) and
[receipt](equivalence-receipt.json) record actual isolated Python startup/env and
streaming comparison against both originals, exit 0/source-equal/empty stderr.
The default verifier mode needs only these encoded files and decoded pins;
--compare-originals additionally requires the exact external source paths. Neither
mode executes commands from an archive or grants runtime admission. The small
historical-equivalence-first generation remains labelled: it preceded adding
an explicit compressed-input window; do not confuse its source pin with current code.

## Placement, retention and next gates

The proposed future output parent is a private 0700 child of existing ignored
shared target on the project disk. The [study](study/analysis.json) records actual
filesystem identities, the /target/ ignore rule and space observations, without
creating that directory. This is one experiment-output location, not a second
cache/checkout or approval store. No selected source, Stage2 input, cache or old
map is moved/deleted. Future space must be checked afresh: 583,532,544 bytes is
the known map/image/log/record footprint, not a reserved/global storage bound.
Unchanged tool environments can still create linker temporaries in /tmp.

[retention-index.json](retention-index.json) maps every retained original or derived
prefix back to source size/hash/path. Original inventories are historical and
can reference external inputs or omitted old benign history; they are not this
publication's manifest. Absolute paths may become unavailable. Retained receipts
and digests cannot reconstruct omitted binaries, archives or linker temporaries.
Recorded source/command bytes are evidence, not reproduction commands to run.
[manifest.json](manifest.json) freezes the publication; verification checks exact
copies, archival equivalence, JSON/AST/links and patch application at the stated base.
Captured data preserves original whitespace; authored prose is checked separately.

First review/retain the proposed operational amendment. Then independently review
new map 128/log 16 monitor/collector code and fresh exact tuple; root must separately
assign a free sole Cargo slot. None is delivered or activated here. Any later
failure still stops without fallback, automatic rerun or wider limits. Ownerful
architecture, full static candidate/native closure, header ABI, exact startup
approval, F4 O/K reservations/quarantine/completion, F6 protected store/context
and immutable admission, checked runtime, C-to-S/SQLite and F7 isolation/credential/
filter/storage/quota/fault/termination evidence remain separate open obligations.
