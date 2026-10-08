# Foreign library and memory provider experiments

> This package is informative and governed by
> [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
> Candidate contracts, syntax, and Core rules are experimental. The
> [execution record](execution.md#current-consolidation-checkpoint) identifies implemented and
> reviewed components. The public SQLite session is verified and integrated on the
> original experimental branch. Basic arena integration is also verified and
> merged. Advanced row/control support is merged into the original branch; the execution
> record identifies connected checks and the final original verification receipt. Experimental
> evidence does not change current Ash semantics.

The first slice establishes a copying SQLite bridge and a fixed-capacity scoped
arena. The next slice compares retained foreign input, temporary output views,
and scoped borrowing. The results must connect author-facing descriptions to
type checking, Core execution, and actual native behavior.

## Experiment inputs

- [Plan](plan.md): bounded steps, files, verification, and advancement criteria.
- [Contracts](contracts.md): native calls, arena requirements, explicit facts,
  inference questions, and trusted assumptions.
- [Cases](cases.md): paired valid and invalid scenarios with expected outcomes.
- [Resource typing, surface, and Core study](semantics.md): resource definitions,
  instance typing, candidate syntax, transitions, and comparison traces.
- [Environment](environment.json): observed native inputs and design snapshots.
- [Authoring log](authoring-log.md): observed friction and candidate assistance
  to evaluate during the implementation.
- [Execution record](execution.md): retained evidence, checkpoint provenance and
  disposition; it has no independent semantic authority.
- [Analysis disposition](analysis-closure.md) and [algebra study](analysis-algebra.md):
  retained F-2 findings, the rejected compound F-1 trial and calibrated admission.
  The former task and execution plans are retired; further algorithmic reduction
  remains a future optimization target.
- [Retained-baseline calibration](https://github.com/dikini/ash-lang/blob/ed3764a15f7f00e7059c3eb3eae1f6e74309040f/docs/design/provider-experiments/resource-calibration/README.md):
  frozen CPU/time/memory measurements, separate admission charges and
  decision-support estimates. The disposition records the later selected
  ordinary admission; further algorithmic reduction remains deferred.

The cases are descriptions to implement, not observed results. Record results
alongside them only after the corresponding checker or native harness runs.
The blueprint and tooling report will be derived from that work, using the
deliverables in DN-0036.

[DN-0037](../DN-0037-ash-authored-foreign-library-interfaces.md) records the
separate program for Ash-authored foreign-library interfaces and generic host
ABI support. It can use this package's findings without adding experiment
inputs or completion requirements.

## Checkout and scope

Run the commands below from the repository root of any checkout containing this
experimental delivery. Use that checkout's Cargo workspace, lockfile and pinned
Rust toolchain. Its branch name or directory does not establish verification;
consult the [consolidation checkpoint](execution.md#current-consolidation-checkpoint)
for the checked source and results.

Historical provenance: the initial experiment used
`/home/dikini/Projects/ash-lang/.worktree/provider-experiments`, branch
`codex/provider-experiments`, from product baseline
`124e164094a9a338fd5ce6a58f979da463285f28`. DN-0034, DN-0035, DN-0036 and the
design index were copied from the main checkout as uncommitted design inputs.
The environment record contains their transfer hashes. Changes to DN-0036 linked
this package; the other carried notes supplied context. These paths describe
that source checkpoint, not a required checkout for reproduction.

The experiment extends parsing, resolution, checking and elaboration in `src/`,
the shared typed Core and the existing Effect evaluator. Source cases use
`driver::run_path` and the integration-test helpers. The adapter crate isolates
unsafe native calls; it does not supply another parser, checker or runtime.
The plan records the proposal and task path needed to adopt successful designs,
specify language changes and establish library APIs.

The additive `driver::run_path_with_foreign_runtime` entry point executes the
experimental native cases. Its `RunConfiguration` carries static manifest
registrations; a separate `ForeignRuntime` carries executable bindings to those
exact original manifests. Static registrations alone do not authorize native
dispatch. Existing `run_path` callers retain their API.

## Reproducing common source cases

From the checkout root, run the public driver tests with one Cargo build job.
These commands execute linked Ash programs and assert native observations.
The commands disable a configured compiler wrapper for reproducibility without
changing Cargo configuration. Their presence is not a new pass receipt:

```bash
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo test -p ash --test provider_sqlite_source copying_sqlite_session_executes_through_public_foreign_runtime -- --exact
```

The SQLite [entry module](../../../tests/fixtures/provider-experiments/sqlite-copying/entry.ash)
opens an in-memory connection, prepares `SELECT ?1`, binds 42, steps and copies
the integer. The test checks
`Completed(Completed(Ok(42), Closed), Closed)` and observes statement
finalization before connection close. The
[SQLite helper](../../../tests/provider_sqlite_source.rs) shows the complete
public binding setup.

The host example also runs all five
[packaged SQLite programs](examples/sqlite-copying/README.md): Unicode TEXT,
copying, file session/reopen, captured resume and owned discard. Build from the
checkout root, then run against a private package copy so the session database
belongs to that copy:

```sh
(
    ash_repo=$(pwd -P)
    CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo build --locked -p ash-foreign-adapter --example sqlite_session || exit
    sqlite_example_dir=$(mktemp -d) || exit
    cp "$ash_repo"/docs/design/provider-experiments/examples/sqlite-copying/*.ash "$sqlite_example_dir"/ || exit
    printf 'Example directory: %s\n' "$sqlite_example_dir"
    cd "$sqlite_example_dir" || exit
    sqlite_example_status=0
    for sqlite_entry in text-entry.ash copying-entry.ash session-entry.ash control-resume.ash control-discard.ash
    do
        "$ash_repo/target/debug/examples/sqlite_session" "$sqlite_example_dir/$sqlite_entry" || sqlite_example_status=1
    done
    exit "$sqlite_example_status"
)
```

This recipe uses the workspace's default `target` directory. If a custom Cargo
target directory is configured, use its `debug/examples/sqlite_session` binary.
Use a fresh private directory for each session run. Keep the printed directory
while reviewing its source, observations and database; remove it afterward.
Check the complete source value and native observations against the package's
required outcomes. A successful host exit alone does not establish source-level
success or successful completion.

The arena [entry module](../../../tests/fixtures/provider-experiments/arena-basic/entry.ash)
uses typed configuration `(64, 4)` and reads native usage `(0, 64, 0, 4)`.
The [public driver setup](../../../tests/provider_arena_source.rs) registers the
original memory manifest and its executable adapter. Reproduce the lifecycle:

```bash
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo test -p ash --test provider_arena_source arena_acquires_queries_actual_usage_and_releases_through_public_driver -- --exact
```

The wider suite covers repeated and nested activations, zero capacities, native
configuration refusal without body or release, dependent access escape rejection,
and release exactly once. The adapter uses the existing physical arena backing;
compiler dispatch contains no arena-specific resource policy. The selected scalar
allocation test connects source allocation and loading to native storage:

```sh
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo test --locked -p ash --test provider_arena_allocation ash_allocates_and_reads_native_storage_before_arena_completion -- --exact
```

Its assertions require `Completed(41, Closed)`, one eight-byte store and load,
matching native owner/allocation identities, one scope release and zero retained
owners. The selected functional checkpoint passes this test and the wider seven-case
allocation suite. The consolidation checkpoint distinguishes that frozen source
from subsequent scanner/lint changes and the pending combined workspace gate. The selected `StorageProvider<R, T>` family covers
finite scalar layouts. Additional payload layouts, general containment, borrowing
and sharing, and providers beyond this selected family remain separate arena work.

The execution record names the verified integration commit for each completed
delivery; later moving-branch receipts remain separate. They test the selected experiment, not current
language semantics or a production architecture. Native adapters must uphold
their ownership, borrowed-view, conversion and destruction contracts; execution
tests do not prove foreign implementation correctness.

Arena owners remain scoped and nontransportable. Aliases can share access while
the owner remains live. Process storage transfer, callbacks into Ash, threads,
async execution, dynamic loading, and tracing implementation are outside the
first slices. Reference counting and tracing remain later comparison questions.

## Setup observations

The system SQLite runtime reports `3.46.1`; its source ID, library hash, and
59 compile options are retained in the environment record. Initial setup found
no `/usr/include/sqlite3.h` or `pkg-config sqlite3` metadata. The copying
[adapter](../../../foreign-adapter/README.md) now uses a pinned matching upstream
header, a checked C shim and the installed runtime soname. The same crate now
also supplies physical arena storage. Its target, ABI checks and native evidence
are recorded in the environment and execution records. Native setup and storage
tests do not establish Ash provider admission or memory checking.

On 2026-10-01 the worktree passed these product baseline checks:

```bash
cargo test --locked -p ash-native-buffer
cargo test --locked --test spec_examples --test resource_scope_runtime --test native_buffer_runtime
```

The adapter suite passed 6 tests. The three root suites passed 78, 14, and 9
tests respectively: 107 tests in total. These checks establish the unchanged
product baseline, not experimental provider admission or FFI conformance.

## Evidence and retention

Every later run records case ID, input revision, candidate, checker outcome,
explicit versus inferred information, Core trace, native observations, costs,
and limitations. A host harness result and an Ash-source result remain distinct.
The experiment is bounded, not required to be disposable. Retain successful
extensions for later product adoption and retain counterexamples that explain
failed candidates. Replace or discard implementation only when the findings
justify it and its useful evidence remains reproducible.

Do not merge unsuccessful candidate machinery. Product adoption requires the
surface syntax and Core semantics, specification, library APIs, review and
verification described in DN-0036. The user's separately authorized 2026-10-08
consolidation may retain the verified bounded implementation in `main` without
adopting its experimental semantics or architecture. Its final merge remains
conditional on combined verification. Paused Lean/Core one-shot work and failed
optimization candidates remain outside that delivery. The execution record
identifies actual results; branch location alone grants no language authority.
