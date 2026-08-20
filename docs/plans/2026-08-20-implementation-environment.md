# Implementation Environment Implementation Plan

<!-- markdownlint-disable MD001 MD036 -->

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Establish the Rust and Cargo workspace, verification entry point, and
dependency-review procedures accepted by AD-0001.

**Architecture:** Start with one empty Ash library at the repository root and a
separate `xtask` package for development automation. Keep the workspace free of
third-party packages, centralize stable lints, and expose one verification
command that any later CI provider can run.

**Tech Stack:** Rust 1.97.1, Cargo 1.97.1, Rust 2024 edition, rustfmt, Clippy,
rustdoc, and rustup target support.

---

Use `@rust-skills` for all Rust and Cargo changes,
`@superpowers:test-driven-development` for the verification runner, and
`@superpowers:verification-before-completion` before every commit and before
finishing TASK-0001.

### Task 1: Pin the stable toolchain

**Files:**

- Create: `rust-toolchain.toml`

**Step 1: Confirm that no repository pin exists**

Run:

```bash
test ! -e rust-toolchain.toml
```

Expected: exit 0.

**Step 2: Add the exact stable toolchain pin**

Create `rust-toolchain.toml`:

```toml
[toolchain]
channel = "1.97.1"
components = ["clippy", "rustfmt"]
profile = "minimal"
```

Do not add deployment targets to the default contributor installation.

**Step 3: Verify the selected compiler and package manager**

Run:

```bash
rustc --version
cargo --version
rustup show active-toolchain
```

Expected: rustc and Cargo report 1.97.1, and rustup reports the repository's
1.97.1 toolchain as active. Rustup may download it on first use.

**Step 4: Commit the pin**

```bash
git add rust-toolchain.toml
git commit -m "build: pin stable Rust toolchain"
```

### Task 2: Create the minimal Cargo workspace

**Files:**

- Create: `Cargo.toml`
- Create: `Cargo.lock`
- Create: `src/lib.rs`
- Modify: `.gitignore`

**Step 1: Verify that Cargo has no project manifest**

Run:

```bash
cargo metadata --format-version 1 --locked
```

Expected: failure because the repository has no `Cargo.toml`.

**Step 2: Add the package and workspace manifest**

Create `Cargo.toml`:

```toml
[package]
name = "ash"
version = "0.0.0"
description = "Implementation foundation for the Ash programming language"
edition = "2024"
rust-version = "1.97.1"
publish = false

[workspace]
resolver = "3"

[lints]
workspace = true

[workspace.lints.rust]
unsafe_code = "forbid"

[workspace.lints.clippy]
correctness = { level = "deny", priority = -1 }
suspicious = { level = "deny", priority = -1 }
style = { level = "warn", priority = -1 }
complexity = { level = "warn", priority = -1 }
perf = { level = "warn", priority = -1 }
undocumented_unsafe_blocks = "deny"

[workspace.lints.rustdoc]
broken_intra_doc_links = "deny"
```

Do not add a `license` field before Ash selects its project license.

**Step 3: Add the empty implementation foundation**

Create `src/lib.rs`:

```rust
//! Implementation foundation for the Ash compiler and runtime.
//!
//! Ash does not yet have implemented language semantics.
```

This file must not introduce syntax, Core forms, evaluator behavior, or other
language claims.

**Step 4: Ignore build output**

Append this entry to `.gitignore`:

```gitignore
/target/
```

**Step 5: Generate and inspect the lockfile**

Run:

```bash
cargo generate-lockfile
cargo metadata --format-version 1 --locked --no-deps
cargo tree --workspace --all-features --locked
```

Expected: Cargo creates `Cargo.lock`; metadata lists only the root `ash`
package; the package tree has no third-party packages.

**Step 6: Run the initial workspace checks**

Run:

```bash
cargo fmt --all --check
cargo check --workspace --all-targets --locked
cargo test --workspace --all-targets --locked
RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps --locked
```

Expected: all commands exit 0. The test command may report zero unit tests and
zero documentation tests.

**Step 7: Commit the workspace foundation**

```bash
git add Cargo.toml Cargo.lock src/lib.rs .gitignore
git commit -m "build: create Rust workspace foundation"
```

### Task 3: Add the provider-neutral verification runner

**Files:**

- Modify: `Cargo.toml`
- Create: `.cargo/config.toml`
- Create: `xtask/Cargo.toml`
- Create: `xtask/src/main.rs`
- Modify: `Cargo.lock`

**Step 1: Add the test before the runner implementation**

Add `xtask` to the root workspace:

```toml
[workspace]
members = ["xtask"]
resolver = "3"
```

Create `xtask/Cargo.toml`:

```toml
[package]
name = "xtask"
version = "0.0.0"
edition = "2024"
rust-version = "1.97.1"
publish = false

[lints]
workspace = true
```

Create `xtask/src/main.rs` with a test that names the required checks before
`verification_steps` exists:

```rust
fn main() {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verification_includes_every_required_check() {
        let labels: Vec<_> = verification_steps()
            .iter()
            .map(|step| step.label)
            .collect();

        assert_eq!(
            labels,
            ["format", "metadata", "build", "clippy", "test", "documentation"]
        );
    }
}
```

**Step 2: Run the test to verify that it fails**

Run:

```bash
cargo test -p xtask verification_includes_every_required_check
```

Expected: compilation fails because `verification_steps` is not defined.

**Step 3: Implement the minimal portable runner**

Replace `xtask/src/main.rs` with:

```rust
use std::{
    env,
    ffi::OsStr,
    process::{Command, ExitCode},
};

#[derive(Debug, Eq, PartialEq)]
struct VerificationStep {
    label: &'static str,
    arguments: &'static [&'static str],
    rustdoc_flags: Option<&'static str>,
}

const VERIFICATION_STEPS: &[VerificationStep] = &[
    VerificationStep {
        label: "format",
        arguments: &["fmt", "--all", "--check"],
        rustdoc_flags: None,
    },
    VerificationStep {
        label: "metadata",
        arguments: &["metadata", "--format-version", "1", "--locked", "--no-deps"],
        rustdoc_flags: None,
    },
    VerificationStep {
        label: "build",
        arguments: &["build", "--workspace", "--all-targets", "--locked"],
        rustdoc_flags: None,
    },
    VerificationStep {
        label: "clippy",
        arguments: &[
            "clippy",
            "--workspace",
            "--all-targets",
            "--all-features",
            "--locked",
            "--",
            "-D",
            "warnings",
        ],
        rustdoc_flags: None,
    },
    VerificationStep {
        label: "test",
        arguments: &[
            "test",
            "--workspace",
            "--all-targets",
            "--all-features",
            "--locked",
        ],
        rustdoc_flags: None,
    },
    VerificationStep {
        label: "documentation",
        arguments: &["doc", "--workspace", "--no-deps", "--locked"],
        rustdoc_flags: Some("-D warnings"),
    },
];

fn verification_steps() -> &'static [VerificationStep] {
    VERIFICATION_STEPS
}

fn verify() -> ExitCode {
    for step in verification_steps() {
        eprintln!("running {} check", step.label);

        let mut command = Command::new("cargo");
        command.args(step.arguments);
        if let Some(flags) = step.rustdoc_flags {
            command.env("RUSTDOCFLAGS", flags);
        }

        match command.status() {
            Ok(status) if status.success() => {}
            Ok(status) => {
                eprintln!("{} check exited with {status}", step.label);
                return ExitCode::FAILURE;
            }
            Err(error) => {
                eprintln!("could not run {} check: {error}", step.label);
                return ExitCode::FAILURE;
            }
        }
    }

    ExitCode::SUCCESS
}

fn main() -> ExitCode {
    let mut arguments = env::args_os();
    let _ = arguments.next();
    let command = arguments.next();
    let extra = arguments.next();

    if command.as_deref() == Some(OsStr::new("verify")) && extra.is_none() {
        verify()
    } else {
        eprintln!("usage: cargo xtask verify");
        ExitCode::from(2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verification_includes_every_required_check() {
        let labels: Vec<_> = verification_steps()
            .iter()
            .map(|step| step.label)
            .collect();

        assert_eq!(
            labels,
            ["format", "metadata", "build", "clippy", "test", "documentation"]
        );
    }
}
```

**Step 4: Add the Cargo alias**

Create `.cargo/config.toml`:

```toml
[alias]
xtask = "run --package xtask --"
```

**Step 5: Run the focused test and full runner**

Run:

```bash
cargo test -p xtask verification_includes_every_required_check
cargo xtask verify
```

Expected: the focused test passes; the runner prints all six check labels and
exits 0.

**Step 6: Confirm that automation added no external packages**

Run:

```bash
cargo tree --workspace --all-features --locked
```

Expected: only the local `ash` and `xtask` packages appear.

**Step 7: Commit the verification runner**

```bash
git add Cargo.toml Cargo.lock .cargo/config.toml xtask
git commit -m "build: add workspace verification runner"
```

### Task 4: Document dependency and contributor procedures

**Files:**

- Create: `docs/project/dependencies.md`
- Modify: `docs/project/README.md`
- Modify: `CONTRIBUTING.md`

**Step 1: Add the dependency-review procedure**

Create `docs/project/dependencies.md` with these sections and requirements:

```markdown
# Dependency policy

This policy applies to Rust packages used for compilation, runtime behavior,
builds, development, and tests.

## Required evidence

Every direct package requires a recorded purpose, dependency role, source,
version requirement, target support, maintenance state, advisory review,
unsafe-code review, license expression, and effect on distributed artifacts.
Review the resolved transitive graph as well as the direct package.

## License compatibility

Evaluate license compatibility as
`compatible(Ash license, dependency license, distribution role)`. The Ash
license is currently an unspecified parameter. Do not replace it with a
provisional allowlist or claim compatibility before the project selects it.

Before that selection, require a machine-readable SPDX expression or a reviewed
license file and record all obligations needed for the later evaluation.
Missing, ambiguous, or unverified license information prevents approval.

## Review procedure

1. State why the standard library or an existing package is insufficient.
2. Classify the package as compiler, runtime, build, development, or test use.
3. Inspect direct and transitive sources, versions, features, targets, advisories,
   license data, unsafe code, and distribution effects.
4. Record the evidence in the task or change that introduces the package.
5. Run the workspace verification command with the updated lockfile.
6. Review this evidence again whenever `Cargo.lock` changes.

Package incompatibility with the pinned stable toolchain prompts review of an
upgrade, feature configuration, replacement, patch, or removal before any
toolchain change. A toolchain downgrade requires explicit review.
```

**Step 2: Link the policy from the project index**

Add this item to `docs/project/README.md`:

```markdown
- [Dependency policy](dependencies.md)
```

**Step 3: Add the contributor commands**

Add a short `Implementation environment` section to `CONTRIBUTING.md` that:

- links AD-0001 and the dependency policy;
- says rustup reads `rust-toolchain.toml` automatically;
- requires `cargo xtask verify` before submission;
- requires dependency evidence whenever `Cargo.toml` or `Cargo.lock` changes;
- states that package trouble does not authorize an automatic toolchain change.

**Step 4: Verify repository prose**

Run:

```bash
markdownlint --disable MD013 -- docs/project/dependencies.md docs/project/README.md CONTRIBUTING.md
git diff --check
```

Expected: both commands exit 0.

**Step 5: Commit the procedures**

```bash
git add docs/project/dependencies.md docs/project/README.md CONTRIBUTING.md
git commit -m "docs: define Rust dependency review"
```

### Task 5: Verify the first deployment target and close the task

**Files:**

- Modify, then remove when complete: `docs/tasks/TASK-0001-establish-implementation-environment.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/trajectory.md`
- Remove when complete: `docs/plans/2026-08-20-implementation-environment.md`

**Step 1: Install the ARM64 Linux standard library**

Run:

```bash
rustup target add aarch64-unknown-linux-gnu
```

Expected: rustup confirms that `rust-std` for the target is installed or already
present.

**Step 2: Compile-check the workspace for ARM64 Linux**

Run:

```bash
cargo check --workspace --all-targets --target aarch64-unknown-linux-gnu --locked
```

Expected: exit 0. This is a compile check, not evidence of native execution.

**Step 3: Run all local verification from a clean diff review**

Run:

```bash
cargo xtask verify
cargo tree --workspace --all-features --locked
git diff --check
markdownlint --disable MD013 -- CONTRIBUTING.md docs/project docs/tasks docs/trajectory.md
```

Expected: all checks exit 0; the package tree lists only local packages.

**Step 4: Record results before removing the active task**

Update TASK-0001 with the toolchain versions, verification output summary,
discovery notes, and any deviations. Commit that progress record so Git retains
it:

```bash
git add docs/tasks/TASK-0001-establish-implementation-environment.md
git commit -m "docs: record environment verification"
```

**Step 5: Remove completed planning artifacts and update current-state indexes**

Remove TASK-0001 and this execution plan. Remove the task from
`docs/tasks/README.md`, restore its statement that no implementation task is
active, and remove the completed implementation-environment row from
`docs/trajectory.md`. Git history retains the decision, task, plan, and evidence.

**Step 6: Verify the final repository state**

Run:

```bash
cargo xtask verify
cargo check --workspace --all-targets --target aarch64-unknown-linux-gnu --locked
git diff --check
markdownlint --disable MD013 -- CONTRIBUTING.md docs/project docs/tasks docs/trajectory.md
! rg -n 'TASK-0001|2026-08-20-implementation-environment' docs
git status --short
```

Expected: all checks before `git status` exit 0; `rg` finds no stale current-tree
references; status shows only the intended task, plan, index, and trajectory
changes.

**Step 7: Commit task completion**

```bash
git add docs/tasks docs/plans docs/trajectory.md
git commit -m "docs: complete implementation environment task"
```
