# Foreign library and memory provider experiments

> This package is informative and governed by
> [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
> Candidate contracts, syntax, and Core rules are experimental. The
> [execution record](execution.md#current-checkpoint) identifies implemented and
> reviewed components. Public Ash-source provider execution remains pending;
> experimental evidence does not change current Ash semantics.

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
- [Execution record](execution.md): active checkpoint ownership and verified
  evidence; it has no independent semantic authority.

The cases are descriptions to implement, not observed results. Record results
alongside them only after the corresponding checker or native harness runs.
The blueprint and tooling report will be derived from that work, using the
deliverables in DN-0036.

[DN-0037](../DN-0037-ash-authored-foreign-library-interfaces.md) records the
separate program for Ash-authored foreign-library interfaces and generic host
ABI support. It can use this package's findings without adding experiment
inputs or completion requirements.

## Worktree and scope

Use `/home/dikini/Projects/ash-lang/.worktree/provider-experiments` on branch
`codex/provider-experiments`. The product baseline is
`124e164094a9a338fd5ce6a58f979da463285f28`. Current DN-0034, DN-0035, DN-0036, and
the design index were copied from the main checkout as uncommitted design
inputs. The environment record contains their hashes at transfer. Changes to
DN-0036 made in this worktree link this package. The other carried notes are
context, not new work performed by this experiment.

Extend the existing Ash implementation in this worktree: parsing and resolution
in `src/`, checking and elaboration, the shared typed Core, and the existing
Effect evaluator. Source cases run through `driver::run_path` and the current
integration-test helpers. Use the root Cargo workspace and lockfile. A focused
adapter crate may isolate unsafe foreign calls within that workspace if needed;
it supplies native primitives, not another parser, checker, or runtime.
Documentation lives here. The plan includes the proposal and task path to adopt
successful code, specify the language changes, and establish library APIs.

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

Do not merge an unsuccessful experiment. A successful branch proceeds through
the adoption steps, including surface syntax and Core semantics, specification,
standard-library APIs, review, and product verification before integration.
