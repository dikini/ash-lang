# Stage 3: exact final-root relink and passive inspection — review only

No relink, readelf, candidate or other native-image execution has run. The lead
currently owns Cargo. Root must assign the exact reviewed tuple and sole cache
slot before any command runs. Four phases have six explicit argv entries:
before verification; monitored relink; after verification; then candidate copy/
bounded ELF preparation, separately monitored readelf, and final receipt.
Neither collector starts hidden child processes. Readelf reads metadata only.

The actual Stage 2 root is
/tmp/ash-owner-generation-stage2/experiment/.ash-build/ash-host-6-0.
Its Cargo/main/toolchain/post-resolution lock and private image/expected-facts
files are all pinned as immutable producer inputs before and after relinking.
The seven Stage 2 files and original receipt are not rewritten. The runtime
fingerprint remains6ed61209 and selected source remains1a8ecef0. The actual CLI
5dca1b62 produced those stored files; Stage 3 does not invoke it or require the
current mutable cache/debug/ash to match historical bytes. Normal Cargo can
reuse compatible dependencies; the cache is neither copied nor cleared.

## Relink mechanism

Only the generated root receives the explicit rustc flags from the earlier
scalar experiment: crt-static, static relocation, explicit /usr/bin/cc with BFD,
-static/-no-pie, strip debuginfo, the exact libc.a and bounded whole-static.map.
There are no global RUSTFLAGS, disabled fingerprints, dependency rewrites,
downloads or alternate caches. These previously successful flags are a proposed
command for this actual owner root, not evidence that it already links.

Normal offline/locked one-job Cargo, JSON artifact messages and verbose tool
commands retain the real root manifest/name/source/executable association. The
candidate preparer requires a fresh actual selected root artifact and successful
build-finished record. Unknown output format or unexpected cache reuse refuses;
there is no automatic retry. Toolchain, ABI headers, native archives, cc/BFD/
bundled-linker observations and all source/generated/tool/config pins are
checked before and after. Changed-cwd Cargo ancestor configs and earlier BFD
lookup paths are absent as declared. These are bounded correspondence checks
under a stable trusted build context, not hostile-writer or complete dynamic
build-tool containment proofs.

## Final candidate and passive inspection

After successful relink and after verification, the preparer checks the actual
linked root is no larger than128MiB, streams its hash and bounded copy to private
static-host, sets the copy to0400, and verifies exact copy equality. The mode
removes executable permission; it is not a memfd seal or startup approval.
Candidate inputs are private but not protected against their owner changing
bytes; before/after hashes and the stable trusted context remain explicit.

A bounded 64-byte ELF header and at most64 program headers must establish ELF64
little-endian x86-64 ET_EXEC, a valid executable LOAD entry, file/segment bounds,
and no PT_INTERP/PT_DYNAMIC. The separately listed readelf -W -h -l -d command
runs under the same reviewed monitor with pinned tool and exact environment.
The finalizer requires actual successful inspection/reaping, matching config,
monitor/output hashes, no dynamic section and unchanged candidate bytes. There
is no ldd, native metadata query, trace, candidate startup or runtime loading.

The full link map is limited to16MiB and hashed. Compact LOAD lines bind every
observed existing regular input by full size/hash; missing linker temporaries or
nonregular inputs are explicit unresolved producer/build-trust limits. This is
not a guarantee that all linked object bytes are independently recoverable or
that retained loading code can never run. Full maps/binaries/headers stay
external; a later evidence PR retains compact source/provenance only.

## Limits and authority

Both tools have1200-second monitored deadlines and16MiB retained combined output;
map/log samples can overshoot and do not quota the shared cache. Actual owned-
family termination/reaping is required, with pending kernel reaping never called
success. New source/text records are1MiB, producer receipt256KiB, manifest4096
records/4MiB; final static image128MiB and program headers64. No evaluator/native
memory limit or new product gas constant is inferred. Receipts are emitted only
after the required predecessors succeed. Any failure stops, preserving partial
evidence, without changing inputs, limits, architecture or approval.

CP-0024 defines the semantic obligations; this legacy owner baseline has no
checked runtime activation. Contract27430/PR1002ac8 authorizes only the bounded
experiment's staged gates. AD-0015 remains owner-free and is not promoted.
Ownerful no-loading/source/ABI/native-truth, host-loss/group reservations,
shutdown and applicable approval/context/store premises remain for independent
assessment and architecture selection. Packaging success would establish static
feasibility for the observed closure, not checked O/K behavior, physical cleanup,
SQLite/isolation acceptance or whole F2 completion. Stop after static receipt.

Map finalization additionally requires recognized GNU/BFD Memory Configuration,
Linker script and memory map, and x86-64 OUTPUT framing, nonempty LOAD records,
and the explicit /usr/lib/x86_64-linux-gnu/libc.a LOAD matching its pinned full
size/hash. Empty or unknown maps cannot become successful receipts. The retained
parser-only controls exercise the actual finalizer functions; their positive
uses synthetic framing and actual pinned archive bytes, not an actual new full
map or closure. Historical pre-repair source/manifest bytes remain separately
pinned. Missing other linker temporaries remain explicit producer-trust limits.
