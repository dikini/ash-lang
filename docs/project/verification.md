# Rust verification

[AD-0014](../decisions/AD-0014-rust-verification-stage-reuse.md) governs this
runner. Run commands from the Git repository root, with the pinned Rust toolchain
and one Cargo job. The milestone PM assigns the heavy-build slot.
The alias builds xtask with the optimized `verification` profile for receipt
hashing. Its child product checks use their existing default profiles.
For candidates whose matching-compiler fingerprint includes the root manifest
and lockfile, a tooling overlay changes that identity. Retain required native
and embedded-image evidence under the original configuration separately.

## Required stages

`cargo xtask verify` runs a fresh complete gate in this order:

| Stage | Evidence |
| --- | --- |
| `format` | Workspace formatting check. |
| `metadata` | Locked workspace metadata without dependencies. |
| `check` | Default-feature type checking of every workspace target. |
| `build` | Default-feature library, binary and example linkage. |
| `clippy` | All-target, all-feature workspace lint with warnings denied. |
| `test` | All-target, all-feature workspace compilation and tests. |
| `documentation` | Workspace rustdoc, no dependencies, warnings denied. |

Default-feature test harnesses are checked but no longer linked by `build`.
The all-feature `test` stage links and runs them. This preserves distinct
default-feature coverage and avoids a second set of integration-test binaries.

## Selecting and reusing evidence

During the edit loop, check the affected package and run the specific target
and cases required by the changed boundary. For example, an xtask receipt
change can start with:

```sh
cargo check -p xtask --bin xtask --locked
cargo test -p xtask --test verify --locked \
  matching_successful_stages_reuse_but_plain_verify_runs_fresh -- --exact
```

These commands provide focused feedback; they do not establish a complete gate
or a canonical stage receipt. Broaden coverage when the task's affected
boundaries require it, and run the governing delivery gate once the change is
ready. Documentation-only work follows the documentation policy's manual
checks unless its governing artifact requires code verification.

Select the package and target as well as the test case. A test-name filter
controls execution within the selected binaries; it does not by itself avoid
compiling unrelated test targets. Changes to shared compiler code can affect
unchanged tests, so coverage follows the changed behavior and its consumers,
not just edited test files. Rustdoc generation is not needed for each test run;
check affected API documentation when it changes and retain the rustdoc stage
where the governing delivery gate requires it.

### Checkouts and build caches

Reuse a suitable active checkout before creating another. Keep a stable target
directory and let Cargo reuse compatible artifacts. A fresh verification command
does not require an empty cache. Do not clean or relocate a cache as a routine
precondition for a gate. Cold builds belong to measurements that require them
or to diagnosis of a demonstrated cache problem.

The PM assigns a single writer to each product cache. Reviewers can inspect the
same frozen source, receipts and logs without allocating another product cache.
When isolation requires another checkout, coordinate access to an existing
compatible cache; changed paths or configurations can still require Cargo to
recompile affected artifacts. Receipt reuse remains bound to its recorded
checkout and inputs.

Estimate storage before a cold comparison. Retain required logs, input records
and native evidence independently of disposable build output. Reclaim owned,
superseded caches once no active owner needs them; preserve the active gate's
cache and evidence.

### Selecting gate stages

At a verification boundary, select only the required gate stages:

```sh
cargo xtask verify --step clippy --step test
```

This records **partial verification**, not a complete gate. Selection does not
decide which checks your task requires; its governing artifact does. Stages run
in the order above even when selected in another order.
The `test` stage still builds and runs every workspace test target. Stage
selection does not select individual test targets or cases.

For an unchanged checkout, complete the remaining checks and reuse matching
successful stages explicitly:

```sh
cargo xtask verify --reuse
```

Reuse requires identical repository files (contents, permissions and symlinks),
external inputs, tool versions and executable pins, runner, environment, Cargo
configuration and stage command. Pins include all existing PATH candidates and
effective rustup components, including the Cargo formatting/Clippy commands.
The saved receipt and its log must still match. A mismatch runs that stage
fresh. A fresh failure retires the older success for those inputs. Input movement
before, during or between checks prevents a successful gate. Reports show
executed and reused stages separately. Plain verification always runs fresh.

The initial input model hashes every tracked file and every non-ignored
untracked file. It intentionally invalidates all stages even for a Markdown
change. It also pins inherited Cargo configuration and the effective environment
(values are hashed rather than exposed). Jobserver and shell bookkeeping are
excluded; `CARGO_BUILD_JOBS` is normalized to the enforced value `1`.
Use the same declared launch environment when sharing receipts across roles.

Git-ignored fixtures and external headers, native archives or other files used
by a check must be named explicitly for reuse:

```sh
cargo xtask verify --reuse --input /absolute/path/to/native/archive.a
```

Repeat `--input` for every such file and use the same list on subsequent runs.
Missing named inputs fail verification. Unrecorded host dependencies, ignored
inputs, or uncertain environment changes require fresh checks. Local receipts
assume trusted storage and a frozen checkout; they are not signed attestations.
Keep review, retention checks, real native observations and acceptance as
separate obligations. Final integrated gates remain fresh unless the governing
artifact explicitly permits evidence transfer.

Custom wrappers can delegate to other tools; name those files with `--input`
when they are not already pinned. Shared host libraries and other ambient host
dependencies remain part of the trusted, unchanged local environment.

## Logs and handoff

The default output is `target/verification/`. Use `--receipt-dir DIR` to choose
another directory; output inside the checkout must be Git-ignored. Per-stage
receipts retain input pins, exact arguments, log hashes and elapsed seconds.
Per-run summaries and `latest.json` record success, complete or partial scope,
executed/reused stages, failures and wall time. Each stage prints its log path.
Deleting
receipts or logs only removes the opportunity for reuse.

A handoff includes the exact source and target commits, stage summary, receipt
and log paths, explicit external inputs, configuration and cache conditions,
and the next owner. A successful partial run never satisfies a full gate.
Markdown, relative links, artifact structure and authority review remain manual
checks under the [documentation policy](documentation.md).

For a before/after measurement, `cargo xtask inputs [--input FILE]...` prints
the same input fingerprint as JSON without running verification stages or
writing receipts. Capture and compare it across both plans. An input dump is
provenance only; it establishes no verification result.
