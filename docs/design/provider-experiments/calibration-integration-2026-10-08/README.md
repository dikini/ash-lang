# Calibration integration, 2026-10-08

Informative implementation evidence for the bounded [DN-0036 experiment](../../DN-0036-foreign-library-and-memory-provider-experiments.md). The preserving merge joins Original `19441bd76f1e322aabe7dcd75e58e59e7efa394e` and Calibration `ed3764a15f7f00e7059c3eb3eae1f6e74309040f`. It retains the separately selected [ordinary admission policy](../calibrated-admission-2026-10-08/README.md); diagnostic completion grants no ordinary admission or checking authority.

The reconciliation selects explicit diagnostic overrides once per complete owner, preserves exact caller/remaining capacities, and emits one final measurement per executed owner. Both Pure and Effect Core use their actual supplied capacity. Partial failure reports remain intact. Generated native measurement tests require explicit invocation; ordinary all-feature runs ignore that environment-dependent harness. New manifests request it with `--ignored`; historical manifests remain unchanged.

Connected verification in the Original worktree passed:

- Default reporting, copying, sessions and control: 22 tests, including the four formerly blocked complete SQLite assertions, without an override.
- Feature-enabled reporting, observer, copying, sessions and control: 24 tests; the generated measurement test is ignored. The observer tests use nine child invocations covering observation ON/OFF, ordinary/explicit diagnostic limits, Pure/Effect paths, nine phase endpoints, six owner endpoints and incomplete Source rejection.
- Explicit generated native harness: one fresh ordinary invocation passes, then the new manifest runner passes observation ON/OFF with its explicit diagnostic allowance. Native connection acquisition and close are observed. This is a tooling smoke check, not a new calibrated CPU/RSS model or optimization claim.
- Focused bidirectional type-carrier inventory: one pass. Review found and corrected 13 missing borrowed surface visitor entries and an ambiguous glob import. The complete architecture suite is deferred to the combined gate.
- Strict Clippy for the feature-enabled library and changed reporting/observer/native/inventory targets, plus formatting and offline runner/budget self-checks: pass.

Reproduce the connected selections with one Cargo job:

```sh
CARGO_BUILD_JOBS=1 cargo test --locked -p ash --test compiler_work_reporting --test provider_sqlite_copying --test provider_sqlite_sessions --test provider_sqlite_control
CARGO_BUILD_JOBS=1 cargo test --locked -p ash --features resource-calibration --test compiler_work_reporting --test resource_calibration_observer --test resource_calibration_native --test provider_sqlite_copying --test provider_sqlite_sessions --test provider_sqlite_control
CARGO_BUILD_JOBS=1 cargo test --locked -p ash --features resource-calibration --test architecture every_production_type_field_is_manifested_bidirectionally -- --exact
CARGO_BUILD_JOBS=1 cargo clippy --locked -p ash --features resource-calibration --lib --test compiler_work_reporting --test resource_calibration_observer --test resource_calibration_native --test architecture -- -D warnings
python3 tools/resource_calibration.py self-check
python3 tools/resource_budget_estimates.py self-check
```

Host execution disabled its unavailable compiler cache with `RUSTC_WRAPPER=`. Builds remained serial and target caches were retained. [Source pins](source-pins.json), [raw verification logs](connected-verification.tar.gz) and [new smoke archive](new-observer-smoke.tar.gz) identify this assembly. The archive contains fresh input, manifest, raw observations and executable hashes; absolute paths identify that historical run. Existing frozen calibration artifacts match their incoming committed blobs exactly. All 26 unrelated Original working inputs were unchanged. Independent source review found no remaining concrete contract issue after the inventory correction.

This checkpoint does not claim the pending arena scalar delivery, final combined `cargo xtask verify`, main integration, worktree cleanup, formal proof or production adoption. The [execution record](../execution.md) records later integration status separately.
