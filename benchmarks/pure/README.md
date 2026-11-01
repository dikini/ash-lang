# Pure computation microbenchmark

Compare equivalent terminating computations in Ash and Python on Linux x86-64
GNU. This is measurement tooling. It changes no language or runtime behavior.

The [2026-11-01 measurement](results-2026-11-01.md) records release-mode results
and their scope.
The [Boolean comparison](boolean-results-2026-11-01.md) measures numeric and
nonnumeric map/fold on one frozen compiler build.

| Case | Computation | Expected result |
| --- | --- | --- |
| `factorial` | Recursively multiply integers 1 through 400; exercises mathematical integers beyond machine range. | `400!` |
| `fibonacci` | Naive branching recursion for Fibonacci 22, using an increasing position and an exclusive end. | `17711` |
| `map_fold` | Construct a 400-element linked list, map `x*x + 3*x + 7`, then fold with addition. | `21656800` |
| `boolean_map_fold` | Construct 400 alternating Booleans, map negation, then fold with XOR. | `false` |

The source pairs use matching recursion, strict evaluation order and operations.
Python represents the linked list with nested pairs and `None`; Ash uses nominal
constructors. Neither implementation memoizes Fibonacci, fuses map with fold,
uses a builtin factorial, or replaces recursion with a loop. The benchmark
driver independently checks the results, using Python's builtin factorial and
the sum formulas as oracles outside the timed processes.

`boolean_map_fold` contains no source-level `Int`, numeric literals or numeric
operators. Its builder doubles and appends existing linked lists, avoiding a
numeric length counter. Both implementations include that construction in the
timed process, map every element and fold every element. Exactly 200 mapped
elements are true, so XOR from false returns false. The numeric and Boolean
cases have different builders; their timing difference does not isolate the
cost of integer operations. Default allocation services and evaluator bookkeeping
remain in the Boolean case.

## Run

Build the compiler in release mode, then run the benchmark from the repository
root. It uses Python 3.11 or newer, its standard library, GNU `/usr/bin/time`,
and the pinned Rust toolchain. Cargo dependencies must already be cached.

```sh
RUSTC_WRAPPER= cargo build --offline --release --bin ash -j 1
RUSTC_WRAPPER= python3 benchmarks/pure/run.py
```

Run just the nonnumeric case with `--case boolean_map_fold`.

`RUSTC_WRAPPER=` bypasses an inherited compiler cache wrapper; omit it when that
wrapper works in the execution environment. Keep the same Rust configuration
for the Ash executable and generated hosts.

The default is five measured runs after one warmup per lane, and one measured
build per case. Increase the sample counts or select a case:

```sh
RUSTC_WRAPPER= python3 benchmarks/pure/run.py \
    --repeats 10 --build-repeats 3 --case fibonacci \
    --output target/pure-benchmark/fibonacci-10
```

`--output` must name a new directory. `--ash` selects another prebuilt compiler;
the runner does not infer its optimization profile. `--cargo-target-dir` selects
the shared host build cache. `--compiler-source-root` selects the matching
compiler checkout whose sources are fingerprinted for new host builds; it
defaults to this repository. Set it when `--ash` was built from a frozen copy.
Commands run sequentially. Lane order is shuffled
with a recorded fixed seed in every round. Do not run other builds or benchmarks
concurrently when collecting comparison results.

To repeat execution measurements on existing artifacts, use `--reuse-builds
PATH/TO/results.json`. The runner checks the compiler binary, both workload
sources and each host against the receipt hashes. It requires equal before/after
input snapshots for the original build and successful build samples. Those
samples and their original source/environment provenance transfer unchanged;
the runner does not measure new builds. Fresh execution samples then use only
the pinned executables and workload sources. This also allows execution against
one compiler version while unrelated compiler sources change in the checkout.
The receipt records the transfer explicitly, including the original cache setup.

## Measurement boundaries

| Lane | Timed work |
| --- | --- |
| `ash_run` | `ash case.ash`: process startup, source loading/checking, Core validation, evaluation, result rendering and teardown. |
| `build` | `ash build --output host --cargo-target-dir cache case.ash`: source compilation, host generation, Cargo compilation/linking, root artifact cleanup and publication. It does not execute the workload. |
| `ash_host` | The generated executable: process startup, embedded Core reconstruction, evaluation, result rendering and teardown. |
| `python` | `python3 -I -B case.py`: isolated Python startup, source compilation, evaluation, result rendering and teardown. |

Ash's generated host embeds checked Core and uses the existing evaluator, as
specified by [AD-0013](../../docs/decisions/AD-0013-generated-native-bridges-and-program-builds.md)
and the [build tool contract](../../docs/tools/ash.md). These measurements do not
evaluate a direct machine-code backend. The numeric cases use mathematical
integers in both languages; see [Ash's primitive rules](../../spec/dynamic-semantics.md#primitive-operations).
Allocation and ordinary runtime services remain part of execution even though
the workload functions perform no external effects.

The runner first builds a trivial host to prime native dependencies in the shared
cache. Its full cost appears separately in the JSON `setup` section. Each
measured workload build creates and links a fresh generated root package with
that cache available. These are warm-cache builds, not clean builds. Building
the Ash compiler itself is preparation outside the benchmark.

For each invocation, the runner records:

- **Wall seconds:** monotonic elapsed time around process creation and completion.
- **User/system CPU seconds:** Linux `wait4` resource usage, retained separately
  and summed as `cpu_seconds`. Waited-for compiler descendants contribute to build
  CPU. This is consumed CPU time, not an instantaneous CPU percentage.
- **Peak RSS KiB:** GNU time's maximum resident set size for the command. For
  builds, this is the largest process peak, including waited-for descendants;
  it is not the sum of simultaneous process-tree memory. It includes resident
  runtime/code pages, not just the language heap.

Wall and CPU time include the small GNU time monitor's overhead in every lane.
RSS excludes that monitor and the Python benchmark driver. Directly using the
driver child's `wait4` RSS would impose the driver's inherited pre-exec memory
footprint on small programs; the native monitor avoids that measurement floor.
Transferred build samples retain the measurement method used by their source
receipt; a sample without `monitor_argv` used direct `wait4`. Its RSS may include
the driver's pre-exec footprint. Treat that value as target RSS only when it
exceeds the established driver floor; otherwise repeat the build with the native
monitor. Execution samples always use the current measurement method.

The table prints medians. `results.json` retains every warmup/build/run sample,
minimum and maximum per metric, commands, output, exit status, timeouts,
source/tool/binary hashes, host hashes, tool versions, Git state, CPU model and
affinity. The executable hash pins the supplied compiler; the local source
snapshot alone does not establish how that executable was built. Generated
host builds enforce compiler/runtime compatibility. Input changes or any
incorrect result make the run fail. Failed commands
and partial measurements remain in an incomplete receipt. Generated host sources
and native build logs remain beside the executables under `.ash-build`.

These are whole-process microbenchmarks on fixed small inputs. Startup,
checking and teardown can dominate; use the three lanes' stated boundaries when
interpreting ratios. One measured build is a single observation. The suite
establishes no general language performance ranking or whole-tree memory bound.
