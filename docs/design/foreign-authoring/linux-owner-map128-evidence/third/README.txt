# Third Stage3 map-only proposal

Preparation only. No relink, readelf, candidate or native startup has run in this
fresh directory. Independent exact tuple/collector review and root assignment
of the sole Cargo slot remain required. The retained amendment is PR102 commit
88db679943c981458b829e1c430e9af290976d9f, parent c8a1fee506a00f68065cb08c6e2e9911d44a58aa,
tree d32739241785a8a84a049e9c2c9c36165538dc77. Its exact contract is
experiment-contract.md, SHA-256 7e81587b5598f1d7184ce268725e2a1296341c8e84415a44de7cc180d65527ef.
The earlier contract 27430 bytes, assignments, maps and receipts remain unchanged.

## Exact proposed change

The root-only static linker arguments are identical to the second failed attempt,
including explicit cc/BFD, static/no-pie, exact libc.a and diagnostic
--no-print-map-discarded. Only the output/map paths and map-specific observation
policy change. No global RUSTFLAGS, fingerprint bypass, source/native/symbol/ABI
change, download, cache duplication, compiler substitution or mode fallback.
All stored Stage2 inputs stay fixed: ash-host-6-0, source, bridge, full plan,
private image/expected facts, Cargo manifest, post-resolution lock and native log.
The historical selected CLI 5dca produced these files but is not invoked here or
required to equal current mutable cache/debug/ash bytes.

Both relink.monitor.json and inspection.monitor.json select exactly
map_relative_path=whole-static.map. The independently reviewed monitor b36fbefc
uses schema 2 and a 67,108,864-byte cap only for that exact relative map. Other
watched whole-static.map paths and native-build.log files, plus combined command
output, retain 16,777,216-byte limits. No self-test overrides appear in either
config. Sampling can overshoot or miss intervening sizes; recorded peaks are
sampled observations, not a quota or proof of an unobserved peak. Missing or
truncated maps never satisfy the collector.

prepare_candidate.py binds actual clean schema 2/class limits to a fresh root
Cargo artifact, before bounded candidate copy/ELF inspection. finalize_static.py
reads at most 64 MiB plus one oversize sentinel for the map; output logs remain
bounded at 16 MiB, receipt 256 KiB, manifest 4096 records/4 MiB, final image 128 MiB,
PH 64 and command 1200 seconds/one job. It requires complete map bytes to match
the settled monitor's full hash/size, recognized GNU/BFD framing, nonempty LOADs
and explicit pinned libc.a LOAD. Existing missing linker temporaries remain
qualified producer/build-trust premises, not a fully hashed native closure.
Suppressed discarded-section diagnostics are disclosed. No old prefix may be
promoted to a complete new map or successful artifact.

## Proposed six-command sequence

The exact argv, cwd and isolated three-key outer environment are in tuple.json.
All wrappers use /usr/bin/python3.14 -I -S -B with an explicit environment;
Cargo/readelf child argv/environment are independently fixed in their configs.
The trusted operator must first compare external tuple/manifest/collector/config/
monitor/interpreter anchors, then run only after an exact root assignment:

1. Read-only before-relink verifier.
2. Monitored offline/locked one-job final-root-only Cargo relink.
3. Read-only after-relink verifier, only after clean relink success.
4. Bounded candidate copy and ELF/header/actual root-artifact collection.
5. Separately monitored pinned readelf metadata inspection.
6. Final complete-map/native association manifest and packaging receipt.

Each step must exit 0. Both monitors must show exit/child 0, all owned children
actually reaped, no final pending/escape/truncation/limit failure. Any failure
stops without repair, rerun, wider cap or fallback. No candidate startup follows
this sequence. A 0400 copied/hash-verified file is not approved sealed-fd
execution or protected artifact approval. Ownerful architecture, exact native ABI,
loading/shutdown premises, checked runtime/O/K, store/context and isolated worker
evidence remain pending separately.

## Read-only preparation evidence

provenance.json binds the retained amendment, independently reviewed monitor
source/schema/benign before-after suite and both real 16 MiB map refusals. The
historical identities/bytes are not changed. The new monitor's benign suite used
reduced synthetic caps; it predicts no successful real map, link or candidate.
The first failed map 17,346,560 bytes and second 17,674,240 bytes were sampled,
possibly incomplete and never fully hashed. Only their exact 16 MiB prefixes
and original receipts are referenced, not copied or silently relabelled.

readonly-check-command.json and preparation-readback.json retain the actual
read-only verifier command/result, not execution of a proposed tuple phase.
It compared all 2784 source blobs/96,452,672 bytes, native/tool/config pins and
stored Stage2 generated inputs. No Cargo/compiler/linker/readelf was invoked.
It observed /tmp available bytes at 1,186,598,912; the before/after verifier will
check and report that value afresh. known_output_footprint in preflight sums
382,205,952 bytes for raw map plus two retained map copies, candidate, two outputs,
monitor receipts and final records. This is a finite known-output preflight floor,
not reserved storage, a global bound on possible intermediates/sidefiles or
protection against concurrent /tmp writers. No unrelated scratch tree, pinned
input or cache is deleted or moved. The shared-cache CLI is not copied.

manifest.json freezes this preparation package. Historical actual records remain
external and byte-pinned; future actual outputs do not yet exist. No candidate
hash or successful native closure is invented before the assigned build.
