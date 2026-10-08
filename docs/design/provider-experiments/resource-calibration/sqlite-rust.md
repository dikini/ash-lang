# Functional Rust SQLite compiler reference, 2026-10-08

This is informational [TASK-0035](../../../tasks/TASK-0035-resource-analysis-relevance-and-fusion.md)
evidence under [DN-0036](../../DN-0036-foreign-library-and-memory-provider-experiments.md).
It adds five working Rust counterparts to the existing Ash SQLite witnesses.
It changes no Ash semantics, compiler limits or optimization decision.

Each counterpart includes the [shared typed Rust bridge](../../../../tools/reference-sqlite/bridge.rs)
in every fresh compiler job. The bridge calls the same system SQLite 3.46.1
and precompiled two-function C copying shim used by the Ash measurements.
Statements borrow their connection; copied values own their storage.
The programs check returned values, operation and copy counts, explicit
successful completion, and statement finalization before connection close.

| Case | Preserved behavior |
| --- | --- |
| [Copying](../../../../tools/reference-sqlite/copying.rs) | Integer, Unicode, blob, empty and null columns, and embedded NUL on output; an owned closure survives both scopes. |
| [Persistence](../../../../tools/reference-sqlite/persistence.rs) | Transaction, three inserts through one reused statement, reset preserving bindings, clear, generic recursive list collection, close and reopen. |
| [Resume](../../../../tools/reference-sqlite/resume.rs) | A one-shot closure resumes with the original live connection and statement; neither is reacquired. |
| [Bound NUL](../../../../tools/reference-sqlite/bound_nul.rs) | The copying helper chain rejects an embedded NUL before native text binding and releases both resources. This is the Ash adapter contract, not a SQLite restriction. |
| [Forwarding](../../../../tools/reference-sqlite/forwarding.rs) | Four generic helpers forward the statement interface; one step returns integer 42 before finalization. |

## Protocol and completed validation

The [frozen protocol](sqlite-rust-protocol.json) pins the Rust sources, direct
compiler, SQLite binary, existing C archive, C source and header before dispatch.
The [runner](../../../../tools/resource_sqlite_reference.py) passed an offline
protocol and immutable-input self-check. Independent source/runner review
found no blocker before dispatch.

One warmup and three measured fresh compiler processes ran for every case
and each of three modes, with no Cargo or incremental compilation:

- **Metadata:** edition 2024, library metadata, opt level 0; type, trait and
  MIR borrow checking plus encoding, without LLVM or native linking.
- **Native O0:** complete executable compilation and linking, opt level 0.
- **Native O3:** complete executable compilation and linking, opt level 3.

All modes use debuginfo 0 and one codegen unit. The two native modes include
monomorphization, code generation and linking against precompiled dependencies.
The metadata mode emits ordinary dead-code warnings because the private entry
is checked as a library. Those diagnostic costs are included; its raw stderr
is preserved. Native compilations produced no diagnostics.

All **60 compiler jobs** completed. All **ten final executable validations**
passed their assertions and exact stdout checks. One version query authenticated
Rust **1.97.1 / LLVM 22.1.6**. There were **71 total target processes**, no
failed attempts or retries, and a **21.958-second** combined window within the
180-second bound. Processes ran serially with a ten-second external timeout.
The host was Linux x86-64, AMD Ryzen 7 7435HS, with 16 logical CPUs.
No Ash, Cargo or C build ran in this round.

## Compiler statistics

These are medians over three fresh measured processes after one warmup.
CPU is native-precision user plus system time of GNU time and its reaped
compiler/linker descendants, excluding Python. Wall is the matching wrapper's
monotonic interval. Peak RSS is GNU time's target process high-water mark,
not allocation bytes or live heap. A linked compiler job may include separate
linker processes; peak RSS is not their simultaneous memory sum.
The raw data retain all three observations, min/max and target GNU metrics.
Rust structural work counters were not measured; CPU and RSS are not converted
into Ash admission charges.

| Case | Mode | CPU ms | Wall ms | Peak RSS MiB |
| --- | --- | ---: | ---: | ---: |
| Copying | Metadata | 134.8 | 135.7 | 109.29 |
| Copying | Native O0 | 384.3 | 358.4 | 133.86 |
| Copying | Native O3 | 830.1 | 807.1 | 136.66 |
| Persistence | Metadata | 113.9 | 114.0 | 110.67 |
| Persistence | Native O0 | 317.1 | 294.0 | 136.30 |
| Persistence | Native O3 | 660.9 | 638.5 | 139.78 |
| Resume approximation | Metadata | 103.2 | 103.1 | 107.91 |
| Resume approximation | Native O0 | 247.7 | 225.2 | 128.14 |
| Resume approximation | Native O3 | 496.9 | 475.3 | 133.79 |
| Bound NUL | Metadata | 104.0 | 104.8 | 108.83 |
| Bound NUL | Native O0 | 276.7 | 258.1 | 132.84 |
| Bound NUL | Native O3 | 591.3 | 569.2 | 135.34 |
| Forwarding | Metadata | 97.6 | 98.2 | 107.13 |
| Forwarding | Native O0 | 231.7 | 209.5 | 126.86 |
| Forwarding | Native O3 | 434.2 | 413.1 | 131.64 |

Compiler threads can consume aggregate CPU exceeding elapsed wall time.
GNU target time has centisecond formatting; wrapper CPU/wall retain finer
precision. Three repetitions describe observed variation, not confidence
bounds. Runtime validation is excluded from these compiler statistics.

## Source size and Ash reference

The Rust source includes the entry and complete shared bridge, counted once
per job. The Ash bytes include its loaded library/provider interfaces from
the existing CPU-precision round. These are lexical byte counts, not equal
AST sizes or checking obligations. Neither includes the source of precompiled
native libraries; Rust's standard library is also precompiled.

| Case | Ash loaded bytes | Rust loaded bytes | Rust lines | Ash CPU ms | Rust metadata CPU ms |
| --- | ---: | ---: | ---: | ---: | ---: |
| Copying | 12,000 | 19,651 | 414 | 184 | 134.8 |
| Persistence | 13,212 | 20,158 | 423 | 229 | 113.9 |
| Resume approximation | 8,677 | 17,959 | 386 | 62 | 103.2 |
| Bound NUL | 11,996 | 19,250 | 409 | 182 | 104.0 |
| Forwarding | 8,240 | 17,769 | 376 | 64 | 97.6 |

Ash numbers are the existing observation-off whole-pipeline measurements,
including loading, checking, independent Core validation and evaluation;
Ash was not rerun here. They are not native executable compilation times.
The Ash measurements used the feature-gated diagnostic allowance of 16,777,216
units (50,331,648 for Core); ordinary production limits remain unchanged.
Completion here does not establish admission under those ordinary limits.
Ash peak RSS was 22–42 MiB; Rust metadata peak RSS was 107–111 MiB.
The current Ash witnesses run within the same broad time scale as these Rust
frontend jobs. This comparison supplies a practical reference; it does not
establish equal work, a performance lower bound, or an optimization target.
It supports retaining the decision to pause open-ended optimization.

The Rust continuation is an operational approximation. It does not capture
an algebraic effect stack or reproduce Ash's provider/effect checks and
independent Core verification. Rust `Completion::Failed` collapses Ash's
consumed/retained failure reports; native-failure paths are not compared.
The Rust integers are `i64`, sufficient for these witnesses and SQLite,
rather than Ash's arbitrary-precision integers. Lifetimes express the
statement/connection dependency but do not reproduce every Ash resource rule.

Optimized executable sizes range from 4,381,552 to 4,433,448 bytes;
unoptimized executables from 4,473,592 to 4,610,672 bytes. These are linked,
unstripped files with statically linked Rust standard-library code and dynamic
SQLite, not runtime memory use or a measure of the resource type overhead.

## Evidence and reproduction

[The evidence index](sqlite-rust-evidence.json) authenticates the raw compiler
and runtime logs, protocol, source/tool snapshots, native bridge archive and
independent audit. [The summary](sqlite-rust-summary.json) retains per-mode
min/median/max. Generated executables and metadata are excluded from the
archive; their byte lengths and hashes remain in every compiler record.
Old calibration archives and indexes are unchanged.

The host sysroot, linker and every transitive system dependency are
not exhaustively captured. Local absolute paths identify measured inputs;
relocate them and freeze a new protocol before reproduction. The C archive
is included, or can be rebuilt separately from the pinned C source/header.
That dependency preparation is outside the compiler measurements.

From the calibration worktree, using the recorded existing native archive:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tools/resource_sqlite_reference.py self-check
PYTHONDONTWRITEBYTECODE=1 python3 tools/resource_sqlite_reference.py run --output NEW_DIRECTORY --rustc /home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/bin/rustc --protocol docs/design/provider-experiments/resource-calibration/sqlite-rust-protocol.json
```

A reproduction needs a coordinated exclusive compiler window and a fresh
output directory. The runner rejects source/native/compiler pin changes,
missing artifacts, unexpected results and timeouts; failed attempts remain
recorded and stop further dispatch.
