# Owner header dependency discovery proposal

PREPARATION ONLY, no GCC or preprocessing has run. [Tuple](tuple.json) supplies four exact commands: known-input verifier, separately monitored dependency-only GCC, after verifier, bounded collector. Root assignment and independent exact review remain required.

The exact C source is the unchanged686-byte prior malloc/free header probe. GCC -M implies -E: it discovers dependencies, does not type-check _Static_assert, compile an object, link or run any image. The later -fsyntax-only pointer/size_t/prototype/target check is a separate frozen gate after discovered headers are reviewed. Header correspondence remains conditional on the explicit x86-64 GNU installed-header configuration; it cannot prove libc implementation, arbitrary ABI behavior, whole native closure, ownerful architecture or runtime permissions.

[Known preflight inputs](preflight-inputs.json) bind actual GCC15 driver and libexec cc1, installed package path lists, driver-bound built-in specs and absent external specs, known seed headers, manual, Python and reviewed64 monitor. Full transitive headers are UNKNOWN. -B selects the pinned helper prefix; its include subdirectory is absent. -nostdinc plus three explicit -isystem roots avoids ambient local includes. The collector requires actual verbose cc1 -E and those exact roots; unknown output refuses. Installed dynamic tool/runtime trust remains explicit, not a complete tool closure assertion.

The frozen actual Stage2 generated main.rs, expected-facts and generation receipt connect the question to fixed malloc(size_t) and free(void*) bridge bindings; no source/native substitution. Numeric/shape source assertions are not credited by discovery.

The raw dependency file is deliberately named native-build.log so the existing basename watcher observes it. It is dependency text, not a native build log. Sampled raw-sidefile/stdout bounds16MiB; collector admits dependency text only up to1MiB before decoding,4096 paths, manifest4MiB, receipt256KiB, command1200s. Sampling is not quota/zero overshoot. The single-map monitor field is absent, so the map128 policy is irrelevant here. Private0700 project directory uses existing ignored target, no new cache or checkout.

[Collector](collect_dependencies.py) permits only supported single-target make syntax and canonical absolute declared-root/source paths. New header hashes are explicitly POST-query snapshots, not proof of bytes previously read. Later syntax review must freeze/recheck the exact closure and dependency set. No query, syntax gate, owner startup or other command is implicitly authorized. [Read-only preparation result](preparation-readback.json) checks known inputs only.

The collector now binds admitted dependency bytes before decode to exactly one
settled canonical monitor record (full hash/stable sizes/device/inode, no prefix,
sidefile_log16MiB) and rechecks the same byte/object pin before final receipt.
[Benign association controls](test_dependency_association.py) exercise this
producer boundary without GCC, real headers or dependency discovery. The first
unexecuted proposal is preserved at /tmp/ash-owner-header-unexecuted-first.
