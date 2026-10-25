# Fresh Stage 3 map-detail attempt — review only

No retry, linker/readelf probe, relink or candidate startup has run. The prior
failed attempt and all its inputs, configs, oversized raw map and actual records
remain unchanged at /tmp/ash-owner-static-stage3. This is a fresh private output
and watch directory, not reuse or relabeling of that failure.

The only proposed linker-option change is root-only
`-C link-arg=-Wl,--no-print-map-discarded`. The map path/output directory also
moves to this fresh attempt. Exact source, generated bridge/private payloads,
post-resolution Cargo lock, two native symbols, native archives/headers/tools,
compiler/debug profile, all other semantic/static flags, one shared cache,
offline/locked one job, six explicit argv, limits and acceptance gates remain.
The historical CLI is not invoked or required to match current cache bytes.

## Actual failure and primary option evidence

The old map was observed at 17,346,560 bytes and refused at the 16,777,216-byte
sampled threshold. Its retained exact 16 MiB prefix starts with archive-member
inclusion records; Discarded input sections starts at byte519242. The remaining
16,257,974 prefix bytes are in that section. No Memory Configuration, Linker
script and memory map, LOAD or OUTPUT marker occurs in the retained prefix.
This describes only a bounded incomplete prefix, not the complete failed map.
No full-map digest, successful link or candidate was established by that attempt.

map-detail-evidence.json pins the exact prefix/failed receipts, installed BFD
manual bytes and package metadata. The local manual documents the proposed flag
as suppressing the discarded/garbage-collected-section list in the map, enabled
by default. It is a diagnostic-output option; it does not disable garbage
collection, change source/native calls, or grant a new semantic policy. The
selected actual route remains explicit cc+BFD, not default bundled LLD.
No tool was invoked to query or test this option during preparation.

Suppressing that diagnostic listing may reduce the map enough, but this is
unobserved. It does not establish the complete retained-section map will fit
16 MiB or the image will fit128MiB/link. New Cargo flag spelling may also change
artifact identities; do not assume candidate bytes equal any older output.
If the new command fails or exceeds any existing bound, stop and retain that
actual result without automatic flag changes, truncation, widening or fallback.

## Unchanged exact gates

Before and after verifiers cover all2784 selected Git inputs and exact stored
Stage2 generated/tool/config/native pins, plus the failed-record/option evidence.
Cargo emits normal JSON/root artifact/source identity and verbose tool records.
Candidate preparation only follows clean monitored relink and after-verification.
The final static image must fit128MiB, ELF64LE/x86-64 ET_EXEC, PH64, executable
LOAD entry and no INTERP/DYNAMIC. Pinned readelf runs separately under the reviewed
monitor. The finalizer still requires recognized GNU/BFD map framing, nonempty
LOADs and the exact explicit libc.a LOAD size/hash. It hashes the FULL new map
only if within16MiB; no prefix can pass as a full map. Existing regular LOAD
inputs are hashed, while missing linker temporaries remain explicit producer/
build-trust limitations. Diagnostic suppression is disclosed; omitted discarded
sections are not falsely described as retained full diagnostic detail.

Command deadline1200s, each tool output16MiB, map/log16MiB, text1MiB,
manifest4096/4MiB and receipt256KiB remain fixed. Sampling may overshoot, not quota
storage; actual owned-child reaping remains mandatory. Candidate is copied with
0400 and never executed. No ABI compile, owner/native startup, memfd admission,
approval store, provisioning, architecture acceptance or checked O/K claim follows.
Root must separately assign the exact independently reviewed fresh tuple and
sole Cargo slot. Lead currently owns Cargo; this directory is staging only.
