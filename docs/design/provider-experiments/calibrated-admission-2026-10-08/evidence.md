# Verification index

The source baseline before this delivery was Common `8e63baaf471c824e591c3becaf90bc8da41d3809`.
The adjacent `final-source-pins.json` authenticates 160 source, configuration,
native and fixture inputs, including independently owned SQLite inputs that
remain uncommitted in Common. `preservation.json` records unchanged unrelated
working files and indices in Common and Original before this commit.

All commands use `CARGO_BUILD_JOBS=1` and run in the Common worktree.

- `cargo check -p ash --all-targets`: passed before the final report representation refinement.
- `cargo test --locked -p ash --test compiler_work_reporting --test provider_arena_source --test provider_control_source --test provider_owner_rows --test provider_retention_source --test provider_sqlite_control --test provider_sqlite_copying --test provider_sqlite_sessions --test provider_sqlite_source`: 69 passed (`connected-2.log`).
- `cargo clippy --locked -p ash --lib --test compiler_work_reporting -- -D warnings`: passed on final source (`clippy-3.log`).
- `cargo test --locked -p ash --no-run --lib --test compiler_work_reporting --test provider_sqlite_copying --test provider_sqlite_sessions --test provider_sqlite_control`: final build passed (`final-build.log`).
- Direct execution of those final binaries, serially: 40 passed (`final-tests.json` and six `*-final.log` files). This covers 18 driver regressions, one exact policy boundary case, four reporting cases and all 17 SQLite copying/session/control cases.

`four-programs.json` records the four originally blocked programs passing with
ordinary public-driver admission and unchanged original value/native assertions.
No diagnostic calibration allowance or source replay was enabled.

Earlier failed build, reporting-fixture and large-error lint attempts remain in
the local `/tmp/ash-calibrated-admission-20261008/` investigation evidence. They
are superseded by the final runs above, not counted as passing verification.
The integrated Original gate and integration commit will be recorded separately.

`offline-adoption-audit.json` authenticates the separate physical-cost adoption
at Calibration `ed3764a15f7f00e7059c3eb3eae1f6e74309040f`: its self-check passed and
29 retained artifacts were byte-identical. Physical assessment remains offline.
