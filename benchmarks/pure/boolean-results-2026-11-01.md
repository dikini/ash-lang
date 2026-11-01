# Boolean map/fold results: 2026-11-01

The nonnumeric case constructs 400 alternating Booleans, maps negation, then
folds XOR from false. Both implementations return `false`. The workload uses
no source-level `Int`, numeric literals or arithmetic operators. Construction,
map and fold all run inside the measured process.

Both cases below use the same freshly built release compiler and generated
hosts, with optimization level 3. Its source is the frozen revision
`2725cc2c01770ab318ec29c54e0263cedeab05f4`. The snapshot matches the original
numeric benchmark compiler inputs and is isolated from ongoing edits in the
shared checkout. No compiler or runtime implementation was changed for this
comparison.

Measured on an AMD Ryzen 7 7435HS with Python 3.12.9 and Rust 1.97.1.
Numbers are medians of five fresh processes after one warmup per case and
execution lane. All 30 measured outputs and six warmup outputs matched.
CPU is user plus system time; memory is peak RSS. Wall and CPU include the
small GNU time monitor overhead. Startup and teardown remain included.

| Case | Execution | Wall ms | CPU ms | Peak RSS MiB |
| --- | --- | ---: | ---: | ---: |
| `map_fold` | Ash source | 165.153 | 161.690 | 16.887 |
| `map_fold` | Ash built host | 153.981 | 153.625 | 8.008 |
| `map_fold` | Python | 16.760 | 16.407 | 9.504 |
| `boolean_map_fold` | Ash source | 117.232 | 117.027 | 17.109 |
| `boolean_map_fold` | Ash built host | 108.783 | 108.561 | 8.145 |
| `boolean_map_fold` | Python | 17.491 | 17.288 | 9.406 |

Each build below is one measured `ash build` after native-cache setup.

| Case | Build wall ms | Build CPU ms | Build peak RSS MiB |
| --- | ---: | ---: | ---: |
| `map_fold` | 530.519 | 566.591 | 144.461 |
| `boolean_map_fold` | 531.962 | 578.520 | 144.137 |

Native-cache setup separately took 294.627 s wall,
294.747 s CPU and 2139.090 MiB peak RSS.
Building the frozen compiler itself is preparation outside this benchmark.

The Boolean host remains slower than Python without source-level numeric
arithmetic. The numeric and Boolean cases use different list builders, so
their timing difference does not isolate the cost of integer operations.
Both Ash hosts still reconstruct checked Core and use the existing evaluator.

Raw samples, commands and input hashes are retained locally in
`target/pure-benchmark/2026-11-01-boolean-control/results.json`; the raw
receipt is not published. The [benchmark guide](README.md) describes the
measurement boundaries.

The measurement command was:

```sh
RUSTC_WRAPPER= python3 -B benchmarks/pure/run.py \
    --ash target/pure-benchmark/frozen-build-cache/x86_64-unknown-linux-gnu/release/ash \
    --compiler-source-root target/pure-benchmark/source-2725cc2c \
    --cargo-target-dir target/pure-benchmark/frozen-build-cache \
    --case map_fold --case boolean_map_fold \
    --output target/pure-benchmark/2026-11-01-boolean-control
```

Use a new output directory when repeating the measurement.
