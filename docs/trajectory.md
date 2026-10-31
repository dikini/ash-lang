# Development trajectory

This is a dependency and implementation-status view. `ffi-ash` names the
accepted current dialect on `main`. The [specification](../spec/README.md)
defines its language rules; the [feature inventory](project/implemented-features.md)
records implementation and execution support.

## Current ffi-ash

| Work | Current status | Accepted design and evidence |
| --- | --- | --- |
| Passive modules, interfaces, explicit kinds, method parameters and relational determination | Implemented | [Modular closure](design/modular-ash/closure.md) and [Lib Ash evidence](design/lib-ash/relational-interfaces-evidence.md) |
| Module/local newtypes, scoped evidence, exact effects, one-shot resume/discard, legacy cells, hooks and cleanup | Implemented | [Effect Ash closure](design/effect-ash/milestone-closure-evidence.md) |
| Human/localized diagnostics and JSON output | Implemented | [AD-0010](decisions/AD-0010-human-diagnostic-presentation-and-localization.md) and [tool guide](tools/ash.md) |
| Passive pointer/void foreign declarations, Address and synchronous readonly Bytes | Accepted and implemented | [DN-0037](design/DN-0037-ash-authored-foreign-library-interfaces.md); [M1 Main integration](https://github.com/dikini/ash-lang/pull/143) |
| Generated Rust bridges and evaluator hosts with explicit static/shared linkage | Accepted and implemented | [AD-0013](decisions/AD-0013-generated-native-bridges-and-program-builds.md); [native tests](../tests/program_build_native.rs) |
| Generic cells, snapshots and retained-payload dependencies | Accepted and implemented | [DN-0053](design/DN-0053-scoped-generic-cells-without-native-owners.md); [checkpoint evidence](design/generic-cell/evidence.md) |
| Lexical regions, default and explicit construction placement, supplied storage, closures, recursive graphs and bulk release | Accepted and implemented | [DN-0054](design/DN-0054-base-lexical-region-memory-contracts.md); [M2 Main integration](https://github.com/dikini/ash-lang/pull/157); [R5 product evidence](https://github.com/dikini/ash-lang/issues/70) |
| Scoped retained continuations, exact restoration, current Probe facts and checked Store release | Accepted and implemented | [DN-0056](design/DN-0056-scoped-continuation-retention-and-library-scheduling.md); [C1-C5 evidence](design/retained-control/README.md); [M3 Main integration](https://github.com/dikini/ash-lang/pull/167) |
| Coroutine selection, recursive drain, cooperative FIFO scheduling and explicit gas safe points | Accepted and implemented | [Scheduling library](../libraries/scheduling.ash); [tests](../tests/scheduling.rs) |
| Two pinned workers, independent roots, copied FIFO byte channels, watches, endpoint settlement and terminal failure retention | Accepted and implemented | [DN-0058](design/DN-0058-pinned-worker-host-and-channel.md); [AD-0017](decisions/AD-0017-pinned-worker-host-and-transport.md); [M4 delivery](https://github.com/dikini/ash-lang/issues/55) |
| Ordinary Work/Ack protocol, codec, producing cleanup and error handling | Implemented | [Source libraries](../libraries/README.md); [protocol tests](../tests/pinned_network.rs); [codec tests](../tests/network_codec.rs) |

Source-native interpretation supports the complete current dialect with admitted
native callbacks. Generated executable images support cells, regions, retained
control, scheduling and pointer/void bridges. They do not encode Network scopes
or operations.

## Not implemented

| Work | Current status | Design owner |
| --- | --- | --- |
| Network operations in generated executable images | Not implemented | [Build architecture](decisions/AD-0013-generated-native-bridges-and-program-builds.md) |
| Usage/lifetime-based automatic placement, nonlexical ownership, alternative object reclamation and moving collection | Not implemented | [DN-0054](design/DN-0054-base-lexical-region-memory-contracts.md), [DN-0055](design/DN-0055-algebra-of-regions-lifetimes-and-ownership.md) |
| General borrowing, region ownership transfer and shared ordinary graphs | Not implemented | [DN-0035](design/DN-0035-region-memory-management-and-verified-providers.md), [DN-0055](design/DN-0055-algebra-of-regions-lifetimes-and-ownership.md) |
| Worker migration, shared Stores, general cancellation and automatic checkpoint insertion | Not implemented | [DN-0051](design/DN-0051-userspace-concurrency-and-scheduling.md), [DN-0056](design/DN-0056-scoped-continuation-retention-and-library-scheduling.md) |
| Full SQLite, numeric ABI slots, out-pointers, callbacks, variadics, structs by value and foreign text readback | Not implemented | [DN-0037](design/DN-0037-ash-authored-foreign-library-interfaces.md) |
| Protected or isolated FFI execution and checked-host deployment | Not implemented; earlier programme superseded | [DN-0057](design/DN-0057-checked-ffi-module-boundaries.md) |
| Source propositions/proofs, proof-plan integration and law-derived test generation | Not implemented | [Proof direction](design/DN-0001-reboot-foundations.md#14-propositions-laws-and-proofs), [DN-0056](design/DN-0056-scoped-continuation-retention-and-library-scheduling.md) |
| Float, filesystem and serialization APIs | Not implemented | [DN-0040](design/DN-0040-floating-point-semantics-and-representation.md), [DN-0039](design/DN-0039-files-and-filesystem-resources.md), [DN-0041](design/DN-0041-typed-serialization-and-data-pipelines.md) |
| Native Ash backend and interactive native execution | Not implemented | [DN-0045](design/DN-0045-native-compilation-and-interactive-execution.md) |
| LSP and agent semantic exploration interface | Not implemented | [DN-0046](design/DN-0046-agent-semantic-exploration-and-feedback.md) |
| Package resolution, persistent compiled modules and separate Ash object linking | Not implemented | [DN-0025](design/DN-0025-library-and-package-milestones.md) |

These extensions have no implied execution order. A later change names its
dependencies and updates implementation, tests and specification together.

## Retired and superseded work

The earlier ffi-ash programme delivered a wider foreign policy API and copying
SQLite, native-buffer and Arena libraries. Its
[original scope](https://github.com/dikini/ash-lang/blob/adddeffe5d135bd03bf5fc30051965e5da70ed24/docs/proposals/CP-0022-ash-authored-foreign-interfaces.md)
and [closure task](https://github.com/dikini/ash-lang/blob/7471200efb1bd90782fcad81be54b992fbd92982/docs/tasks/TASK-0041-ffi-ash-milestone-closure.md)
are historical. Those libraries and compiler-managed foreign owner/provider,
status, window, codec and manifest/adapter execution routes are retired. The
accepted pointer/void design supersedes that description of current Ash.

The checked-host F1-F8 assignments, whole-image AD-0015/AD-0016 choices,
protected-launch programme and isolated/full-SQLite requirements are superseded.
Their recorded probes remain historical evidence. The protocol-specific network
checker and one-way completion checker are retired; ordinary Ash implements the
current Work/Ack protocol and handles its errors.

## Historical checkpoints and proof evidence

`mini-ash`, `modular-ash`, `lib-ash`, `effect-ash`, `diag-ash` and `ffi-base`
retain earlier checkpoints. Their names and contents are unchanged. There is no
current compiler dialect selector, compatibility grammar or new ffi-ash tag.
The historical Mini-Ash and Modular Ash closure reports retain their original
inventories and verification. The [migration repair evidence](design/migration-repair-evidence.md)
records subsequent Main repairs; the external ash-doc project owns its migration.

The [lexical-region model](design/lexical-regions/README.md),
[retained-control models](design/retained-control/README.md) and
[one-shot formalization](design/direct-effects/one-shot/README.md) are implemented
proof models with their own theorem scopes. They are not extra source-language
features. Historical worker/ledger and one-way checker results retain their
original conditions; the current ordinary protocol does not use those checkers.
