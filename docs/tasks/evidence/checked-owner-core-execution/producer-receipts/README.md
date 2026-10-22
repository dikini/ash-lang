# Producer receipt verification

This candidate implements opt-in producer observations and independent bounded
receipt decoding under [TASK-0053](../../../TASK-0053-checked-owner-core-execution.md).
It was tested on retained milestone `f4a3a0481aceea879c13c924e13f3b1c0560d831`
plus the source pins in [the reviewed manifest](reviewed-source-manifest.json).
It does not implement protected approval, immutable execution, or checked native
activation. The broad task criteria remain open.

The first exact receipt test and then its seven-test module passed (eight test
occurrences). Their original receipts and inventory are retained with the
`initial-` prefix. After the integration test was added, the final frozen batch
passed all seven receipt tests, 17 affected unit regressions, Clippy with warnings
denied, and one genuine public compile/link-only integration test: 25 distinct
tests. The generated-host build log contains three existing `non_snake_case`
warnings; the root-package Clippy check is clean. [The batch results](batch-results.json) contain the exact selectors,
commands, counts, source equality, Cargo artifact correspondence and cleanup.
[The runner](verify-run.py) and [reviewed proposal](focused-proposal.json) describe
the finite execution and resource observations. All 11 phases exited zero, with
identical 3,724-file input maps and reaped children; their owned process groups
were empty at completion. This is not a host-global process assertion.

The integration test compiled the existing native counter C fixture into one
static archive, then called the public preparation/build APIs. It never started
the generated executable or called its foreign functions. Default and opt-in
preparation both used 69,335 existing preparation work units. The actual final
ELF was 476,001,680 bytes, SHA-256
`5169be2349f0635cdc189190b1f944cccfdea0b7096ea8525280fcb5461ba278`.
The independently decoded [750-byte producer receipt](producer-receipt.bin) has
SHA-256 `67712ef82dd767d7a039914d0afddcbee07c613def9e78283585166fa3726354`.
[The post-link observations](post-link-observation.json) bind the emitted program,
expected facts, generated Rust, source/native inputs, seed and resolved lock,
actual final file, tool arguments and retirement checks. The published staging
copy and unique Cargo root/depinfo were retired; the observed output is retained
externally for review. Loading, native behavior and immutable future execution
were not established.

These are existing-profile observations with explicit 1 GiB artifact, 4,096-byte
receipt, 64-record and 2 GiB receipt-work bounds. They are not strict checked
policy. Missing checked/native/header/tool/policy/premise/context closure remains
explicit. Even independently decoded matching claims with all fields populated
cannot approve or activate anything; current checked applicability and protected
activation refuse. Existing public checked execution guards remain closed.

[Provenance](provenance.json) maps every retained original or deterministic gzip
container to the original decoded size and SHA-256. [The execution inventory](execution-manifest.json)
pins all 72 external final-run records, including repeated before/after maps and
resource samples. One complete final input map is retained as
[compressed JSON](final-source-map.json.gz); other identical maps are referenced
rather than duplicated. Compressed raw logs retain their original bytes after
decoding. Binaries, archives, object files and caches are external omissions,
not missing approval evidence filled by a claim. Original external paths are
live review locations, not durable protected storage.

The final batch observed a minimum 7,594,737,664 available-memory bytes during
its post-link phase. Sampled owned-group RSS reached 5,136,670,720 bytes.
Apparent shared-cache size excluding the independently assigned `parallel-f3`
cache changed from 215,984,337,059 to 220,084,438,345 bytes. Samples are neither
quotas nor complete peak guarantees. The exact cache observations are retained
[before](cache-before.json) and [after](cache-after.json).

The final command phases totalled 397.951 seconds (145.873 seconds for Clippy
and 234.549 seconds for the integration command). This is command wall time,
not total task or model time. The assigned developer was Sol6.1 medium; exact
model runtime is unavailable. Independent review and integration are separate.
