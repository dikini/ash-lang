# TASK-0001: Establish the Implementation Environment

- ID: `TASK-0001`
- Status: active
- Related: [AD-0001: Implementation Environment](../decisions/AD-0001-implementation-environment.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- AD-0001 authorizes Rust and Cargo as the implementation environment.
- Rust 1.97.1 is the current stable release when this task starts.
- The Ash project license remains unspecified. Dependency license review must
  preserve that unknown as an input rather than assume an allowlist.

## Work

- Pin Rust and Cargo 1.97.1 with the formatting and lint components.
- Create a Cargo workspace and an empty Ash library foundation without language
  behavior or third-party packages.
- Commit the lockfile and ignore Cargo build output.
- Configure workspace lints and forbid unsafe code in the initial library and
  development tooling.
- Provide a provider-neutral `cargo xtask verify` command for formatting,
  metadata, build, lint, test, and documentation checks.
- Document package review, license evidence, target support, advisory review,
  unsafe-code review, and lockfile-change requirements.
- Document the contributor setup and verification commands.
- Compile-check the workspace for ARM64 Linux as the first deployment-target
  check. Native platform claims remain future release evidence.

The execution steps are in the
[implementation plan](../plans/2026-08-20-implementation-environment.md).

## Progress

The implementation environment is complete. `rustc --version` reports
`rustc 1.97.1 (8bab26f4f 2026-07-14)`, and `cargo --version` reports
`cargo 1.97.1 (c980f4866 2026-06-30)`. The workspace contains the empty `ash`
library and the `xtask` verification package, with no third-party packages.

## Verification

- `rustc --version` and `cargo --version` report 1.97.1.
- `cargo xtask verify` succeeds with the committed lockfile.
- `cargo check --workspace --all-targets --target aarch64-unknown-linux-gnu --locked`
  succeeds after installing that standard-library target.
- `cargo tree --workspace --all-features --locked` contains no third-party
  packages.
- Documentation links resolve, Markdown lint passes apart from the repository's
  existing line-length convention, and `git diff --check` succeeds.

`cargo xtask verify` ran the format, metadata, build, Clippy, test, and
documentation checks successfully. The workspace test run passed one `xtask`
unit test and reported no `ash` tests. The ARM64 Linux compile check succeeded
for `ash` and `xtask`; it did not execute either package on that target.

## Discoveries

- The repository has no CI-provider configuration or Git remote. The task
  therefore establishes one portable verification command without selecting a
  CI service.
- The locally active stable toolchain was 1.94.0 when the task started; rustup
  reported 1.97.1 as the available stable update.
- Rustup installed the `aarch64-unknown-linux-gnu` standard library for the
  pinned toolchain. The target compile check required no package changes.
- The resolved package tree contains only the local `ash` and `xtask` packages.

## Deviations

- The plan's final broad `TASK-0001` search also matched the artifact guide's
  generic task-filename example. The stale-reference check instead searched for
  the completed task's full filename. The artifact guide remained unchanged.
