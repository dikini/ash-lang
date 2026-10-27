# Developing and verifying proofs efficiently

[AD-0012](../decisions/AD-0012-proof-development-feedback-and-build-reuse.md)
separates local language-server feedback from frozen integration evidence.
Use [Lean navigation](proof-lsp.md) to inspect declarations and proof states.
Use Rust analyzer for symbols, hover, definitions, references and diagnostics.
The pinned Rust toolchain includes the `rust-analyzer` component; installing the
toolchain supplies it. Activate one Rust workspace at a time and stop language
servers before a heavy build on a constrained host.

## Reviewed Lean integration

Run the tracked integration runner from the repository root with Python 3.11
or later on Linux. Its cache and scheduler
use only the Python standard library; the optional MCP has its own environment.

```bash
python3 tools/lean/integrate.py /absolute/path/to/reviewed-batch.json
```

It accepts the existing v5 reviewed-batch configuration: `worktree`,
`parent_head`, `parent_evidence`, `parent_evidence_sha256`, `output_prefix`,
`components`, `new_registered_order`, and optional `insert_before`. Each
component pins its checkpoint, independent review, module sources and expected
axiom-report names and requires `root_verified_review_pass: true`. That field
records an actual completed review; setting it does not perform a review.

The worktree HEAD, parent source/registration pins and reviewed source bytes
must match. The runner freezes the requested sources and computes the union of
old and new reverse consumers. Unaffected parent artifacts and logs retain
their validated hashes. The compiler is resolved through `elan` in the proof
directory, or the configuration's explicit `compiler` path; its version and
hash must match the parent evidence.

The optional `proof_directory` selects a reviewed repository-relative root:
`docs/design/direct-effects/one-shot` (unchanged default),
`docs/design/lexical-regions`, or `docs/design/retained-control`. The runner
rejects other paths, symlink escapes and a parent evidence record for another
root. Non-default evidence must name
its root explicitly.

A new root may begin with an explicitly labelled `seed_kind: empty-registration`
parent: empty module registration, records and imports, zero reports, and only
exact `check.sh`/`lean-toolchain` source pins plus the existing compiler/library
pins and version. This seed claims no prior proof or artifact. New sources still
require reviewed components and pass the same compilation, import, report,
axiom, resource and final-coherence checks. It does not authorize rebuilding or
copying unrelated one-shot proofs to make a mismatched parent fit.

Optional settings are:

| Setting | Default | Meaning |
| --- | --- | --- |
| `jobs` | `1` | One or two ready compiler jobs within this runner |
| `memory_mb` | `4096` | Lean allocation limit per compiler process |
| `headroom_mb` | `4096` | Host memory reserved beyond running-job reservations |
| `module_cache` | `<worktree>/target/lean-module-cache` | Successful receipts |

Each compiler uses one thread, warnings as errors and its allocation limit.
Before starting a job the scheduler checks Linux `MemAvailable` against the
headroom plus a full reservation for each running job. Lean's allocation limit
does not cap the total RSS of every process on the machine. The shared host lock
excludes another module runner. A process inventory counts other Lean, Lake,
Rust and linker jobs and admits at most two compiler processes at launch across
that inventory and this runner. Unmanaged processes can start later; this
check cannot control them. LSP workers still require coordination. A resource
refusal retains existing successes
and reports the pending work instead of waiting indefinitely.

The runner emits per-module progress with wall seconds and peak RSS in KiB
from the compiler's `wait4` resource usage.
`<output_prefix>-module-progress.json`
records successes, failures, blocked consumers, pending work, cache hits and
the maximum running job count. Successful receipts are written immediately
after exit status, log, report, axiom and selected-import checks. A failed
module blocks its consumers while independent ready modules can finish.

The final summary separates affected consumers, actual fresh compilations,
receipt hits and total reuse. `all_modules_fresh` is true only when every
registered module actually compiled in this integration; a successful receipt
hit does not count as a fresh compilation.

Receipts include the source hash, compiler/library pins, compiler options,
expected reports, selected direct-import artifact hashes and runner hash.
Reuse verifies these inputs and the stored artifact and log hashes, rechecks
the log and confirms the paths Lean selects. Cache files are copied into a
new output cache; subsequent compilation cannot overwrite the stored receipt.
Keep the same module store when retrying with a fresh `output_prefix`.
Successful work remains reusable even if another branch failed. Changing a
dependency, source, compiler, options or expected reports invalidates its key.

Only a completely successful batch can pass the final source, compiler,
configuration, review and import-coherence sweep and emit `-evidence.json`.
Partial progress and module receipts do not establish integration. The
`-productive-replay.sh` file is a serial reference script; the scheduler
executes the modules. Its evidence records the actual scheduler and commands.
Python assertion checks are required; the runner rejects `python -O`.

## Choosing a batch

Group related changes when they share reverse consumers and have stable
interfaces. Check an uncertain change to a heavily imported foundation early,
then batch its consumers once the interface settles. Independent changes can
finish separately without waiting for a larger batch.

Use the progress records to compare first-pass success, time per module,
consumer fanout and work reused after failure. A larger batch helps when the
compile time saved exceeds the extra diagnosis, rework and waiting it causes.
Successful receipts reduce retry cost, but they do not remove interface risk.
Avoid edits to frozen inputs or the runner while a build is running.

## Repeating measurements

Replay a previously validated closure in a separate output directory:

```bash
python3 tools/lean/replay.py /absolute/path/to/integration-evidence.json \
  --sha256 EVIDENCE_SHA256 --output target/timing-serial
```

The replay checks frozen source, artifact, log and import pins, copies its
inputs, and recompiles the evidence's affected closure. It writes `result.json`
with per-module wall time and RSS. It does not create new integration evidence.
Use a fresh output and receipt store for a cold two-job comparison; pass
`--jobs 2` only in a resource window. Pass `--module-cache` pointing to the
previous run's receipt store to measure successful-work reuse.

Verify tooling changes with:

```bash
python3 -m unittest discover -s tools/lean -p test_module_build.py
python3 -m unittest discover -s tools/lean -p test_lsp.py
target/lean-lsp-mcp/.venv/bin/python -m unittest discover \
  -s tools/lean -p test_lsp_upstream.py
bash -n tools/lean/lsp-install.sh
```

The module tests invoke actual Lean on tiny modules. They cover dependency
ordering, resource refusal, recovery after failure, source/import/options
invalidation, corrupt artifacts, report mismatch and forbidden proof evidence.
The LSP pin tests start no compiler. Run tests and smoke requests in a resource
window, then retain the frozen integration gate for any proof changes.

## Measured first increment

The [measurement record](proof-tooling-measurements.json) pins the frozen
29-module completion closure used on 2026-10-03. These runs used the same final
runner, compiler, sources and options with fresh module receipt stores:

| Run | Total wall time | Modules compiled | Maximum jobs |
| --- | --- | --- | --- |
| One job | 335.3 s | 29 | 1 |
| Two jobs | 223.1 s | 29 | 2 |
| Reuse successful receipts | 6.9 s | 0 | 1 |

The two-job run took 33% less elapsed time in this comparison. Background
alignment compilation varied, so this is an observed result, not an isolated
speedup estimate. The largest individual compiler RSS was about 3.6 GiB.
The sum of individual peaks for overlapping jobs gives a conservative 6.5 GiB
upper bound for their combined RSS; it includes shared pages more than once
and is not a measured peak of physical memory use.

An earlier two-job attempt detected two other host compilers and launched none.
The final reuse run validated all 29 successful receipts and performed zero
module compilations. It still checked dependency selection through Lean's
lightweight `--deps` queries. Source/artifact preparation and receipt checks
account for the remaining time.

A comment-only delta exercised the complete integration gate on the 1,035-module
registry: one affected module compiled, 1,034 parent modules reused, and all
13,388 reports retained. A fresh-prefix retry reused that module's validated
receipt. The compilation and validation stage decreased from 1.41 to 0.45
seconds; preparation took 6–8 seconds. This is evidence of avoided
compilation, not a forecast for every batch.

Rust analyzer 1.97.1 successfully returned the evaluator's document symbols,
the hover type of `Instantiation`, its definition in
`src/eval/instantiation.rs`,
and an empty diagnostic list for `src/eval/machine.rs`. The workspace was
deactivated before the heavy replay to free its approximately 1.2 GiB RSS.
Lean's verified MCP requests and remaining setup limits are recorded in the
[navigation guide](proof-lsp.md).
