#![cfg(unix)]

use std::{
    fs,
    os::unix::fs::PermissionsExt,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "ash-verify-test-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        fs::create_dir_all(root.join("target/bin")).unwrap();
        fs::create_dir(root.join(".cargo")).unwrap();
        fs::write(root.join(".gitignore"), "/target/\n").unwrap();
        fs::write(root.join("input.rs"), "original input\n").unwrap();
        fs::write(root.join(".cargo/config.toml"), "[build]\njobs = 1\n").unwrap();
        let fixture = Self(root);
        for arguments in [["init", "-q"].as_slice(), ["add", "."].as_slice()] {
            assert!(
                Command::new("git")
                    .args(arguments)
                    .current_dir(&fixture.0)
                    .status()
                    .unwrap()
                    .success()
            );
        }
        let stub = r#"#!/bin/sh
set -e
if [ "$1" = "--version" ] || [ "$1" = "-vV" ]; then
    printf 'fixture-tool-version\n'
    exit 0
fi
printf '%s\n' "$*" >> target/invocations
if [ -f target/fail ] && [ "$(cat target/fail)" = "$1" ]; then
    printf 'deliberate tool failure\n' >&2
    exit 1
fi
if [ -f target/mutate ]; then
    printf 'changed during command\n' >> input.rs
fi
if [ "$1" = "clippy" ] && [ -f helper ]; then
    ./helper
fi
if [ "$1" = "clippy" ] && [ -L input-link ]; then
    [ "$(readlink input-link)" = missing-first ]
fi
if [ "$1" = "build" ] && [ -f target/use-native-tools ]; then
    cc --fixture-compile
    ar --fixture-archive
fi
printf 'fixture command succeeded\n'
"#;
        for name in [
            "cargo",
            "rustc",
            "rustdoc",
            "rustfmt",
            "clippy-driver",
            "cargo-fmt",
            "cargo-clippy",
            "cc",
            "ar",
        ] {
            let path = fixture.0.join("target/bin").join(name);
            fs::write(&path, stub).unwrap();
            fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
        }
        fixture
    }

    fn command(&self, arguments: &[&str]) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_xtask"));
        let path =
            std::env::join_paths([self.0.join("target/bin"), "/usr/bin".into(), "/bin".into()])
                .unwrap();
        command
            .arg("verify")
            .args(arguments)
            .current_dir(&self.0)
            .env("PATH", path)
            .env("CARGO", self.0.join("target/bin/cargo"))
            .env("RUSTC", self.0.join("target/bin/rustc"))
            .env("RUSTDOC", self.0.join("target/bin/rustdoc"))
            .env("RUSTFMT", self.0.join("target/bin/rustfmt"))
            .env(
                "CLIPPY_DRIVER_PATH",
                self.0.join("target/bin/clippy-driver"),
            )
            .env("CC", self.0.join("target/bin/cc"))
            .env("AR", self.0.join("target/bin/ar"))
            .env("CARGO_TARGET_DIR", self.0.join("target"));
        command
    }

    fn run(&self, arguments: &[&str]) -> Output {
        self.command(arguments).output().unwrap()
    }

    fn calls(&self) -> Vec<String> {
        fs::read_to_string(self.0.join("target/invocations"))
            .unwrap_or_default()
            .lines()
            .map(str::to_owned)
            .collect()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn success(output: &Output) {
    assert!(
        output.status.success(),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn fresh_gate_checks_default_features_without_linking_duplicate_test_harnesses() {
    let fixture = Fixture::new();
    success(&fixture.run(&[]));
    assert_eq!(
        fixture.calls(),
        [
            "fmt --all --check",
            "metadata --format-version 1 --locked --no-deps",
            "check --workspace --all-targets --locked",
            "build --workspace --lib --bins --examples --locked",
            "clippy --workspace --all-targets --all-features --locked -- -D warnings",
            "test --workspace --all-targets --all-features --locked",
            "doc --workspace --no-deps --locked",
        ]
    );
}

#[test]
fn matching_successful_stages_reuse_but_plain_verify_runs_fresh() {
    let fixture = Fixture::new();
    success(&fixture.run(&["--step", "clippy", "--step", "documentation"]));
    assert_eq!(fixture.calls().len(), 2);
    let partial = fs::read_to_string(fixture.0.join("target/verification/latest.json")).unwrap();
    assert!(partial.contains("\"complete_gate\": false"));
    success(&fixture.run(&["--reuse"]));
    assert_eq!(fixture.calls().len(), 7);
    let reused = fixture.run(&["--reuse"]);
    success(&reused);
    assert_eq!(fixture.calls().len(), 7);
    assert!(String::from_utf8_lossy(&reused.stderr).contains("7 reused"));
    success(&fixture.run(&[]));
    assert_eq!(fixture.calls().len(), 14);
}

#[test]
fn changed_tracked_untracked_configuration_and_environment_inputs_invalidate_reuse() {
    let fixture = Fixture::new();
    let args = ["--step", "clippy", "--reuse"];
    success(&fixture.run(&args));
    fs::write(fixture.0.join("input.rs"), "changed input\n").unwrap();
    success(&fixture.run(&args));
    fs::write(fixture.0.join("fixture.ash"), "new untracked input\n").unwrap();
    success(&fixture.run(&args));
    fs::write(fixture.0.join(".cargo/config.toml"), "[build]\njobs = 2\n").unwrap();
    success(&fixture.run(&args));
    success(
        &fixture
            .command(&args)
            .env("RUSTFLAGS", "--cfg changed")
            .output()
            .unwrap(),
    );
    assert_eq!(fixture.calls().len(), 5);
}

#[test]
fn declared_external_inputs_are_pinned_and_invalidated() {
    let fixture = Fixture::new();
    let external = fixture.0.join("target/native-input.a");
    fs::write(&external, "original archive").unwrap();
    let args = [
        "--step",
        "build",
        "--reuse",
        "--input",
        external.to_str().unwrap(),
    ];
    success(&fixture.run(&args));
    success(&fixture.run(&args));
    assert_eq!(fixture.calls().len(), 1);
    fs::write(&external, "changed archive").unwrap();
    success(&fixture.run(&args));
    assert_eq!(fixture.calls().len(), 2);
    fs::remove_file(&external).unwrap();
    assert!(!fixture.run(&args).status.success());
    std::os::unix::fs::symlink("missing-archive", &external).unwrap();
    assert!(!fixture.run(&args).status.success());
}

#[test]
fn missing_or_modified_saved_logs_force_fresh_execution() {
    let fixture = Fixture::new();
    let args = ["--step", "clippy", "--reuse"];
    success(&fixture.run(&args));
    let logs = fixture.0.join("target/verification/logs");
    let log = fs::read_dir(&logs).unwrap().next().unwrap().unwrap().path();
    fs::write(log, "edited success log").unwrap();
    success(&fixture.run(&args));
    for entry in fs::read_dir(logs).unwrap() {
        fs::remove_file(entry.unwrap().path()).unwrap();
    }
    success(&fixture.run(&args));
    assert_eq!(fixture.calls().len(), 3);
}

#[test]
fn failures_and_moved_inputs_never_publish_reusable_success() {
    let fixture = Fixture::new();
    let args = ["--step", "clippy", "--reuse"];
    fs::write(fixture.0.join("target/fail"), "clippy").unwrap();
    assert!(!fixture.run(&args).status.success());
    fs::remove_file(fixture.0.join("target/fail")).unwrap();
    success(&fixture.run(&args));
    assert_eq!(fixture.calls().len(), 2);

    fs::write(fixture.0.join("target/mutate"), "").unwrap();
    let changed = fixture.run(&["--step", "build", "--reuse"]);
    assert!(!changed.status.success());
    assert!(String::from_utf8_lossy(&changed.stderr).contains("inputs changed"));
    fs::remove_file(fixture.0.join("target/mutate")).unwrap();
    success(&fixture.run(&["--step", "build", "--reuse"]));
    assert_eq!(fixture.calls().len(), 4);
}

#[test]
fn a_failed_fresh_rerun_retires_an_older_success_for_the_same_inputs() {
    let fixture = Fixture::new();
    success(&fixture.run(&["--step", "clippy"]));
    fs::write(fixture.0.join("target/fail"), "clippy").unwrap();
    assert!(!fixture.run(&["--step", "clippy"]).status.success());
    assert!(
        !fixture
            .run(&["--step", "clippy", "--reuse"])
            .status
            .success()
    );
    assert_eq!(fixture.calls().len(), 3);
}

#[test]
fn changed_tool_bytes_and_deleted_tracked_inputs_invalidate_reuse() {
    let fixture = Fixture::new();
    let args = ["--step", "clippy", "--reuse"];
    success(&fixture.command(&args).env("CC", "cc").output().unwrap());
    let tool = fixture.0.join("target/bin/cc");
    let mut bytes = fs::read(&tool).unwrap();
    bytes.extend_from_slice(b"\n# changed tool, unchanged version\n");
    fs::write(tool, bytes).unwrap();
    success(&fixture.command(&args).env("CC", "cc").output().unwrap());
    fs::remove_file(fixture.0.join("input.rs")).unwrap();
    success(&fixture.command(&args).env("CC", "cc").output().unwrap());
    assert_eq!(fixture.calls().len(), 3);
}

#[test]
fn reuse_refuses_an_unpinned_subdirectory_checkout() {
    let fixture = Fixture::new();
    fs::create_dir(fixture.0.join("nested")).unwrap();
    let output = fixture
        .command(&["--reuse"])
        .current_dir(fixture.0.join("nested"))
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("Git repository root"));
    assert!(fixture.calls().is_empty());
}

#[test]
fn changed_executable_permissions_cannot_reuse_a_previous_success() {
    let fixture = Fixture::new();
    let helper = fixture.0.join("helper");
    fs::write(&helper, "#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&helper, fs::Permissions::from_mode(0o755)).unwrap();
    assert!(
        Command::new("git")
            .args(["add", "helper"])
            .current_dir(&fixture.0)
            .status()
            .unwrap()
            .success()
    );
    let args = ["--step", "clippy", "--reuse"];
    success(&fixture.run(&args));
    fs::set_permissions(&helper, fs::Permissions::from_mode(0o644)).unwrap();
    assert!(!fixture.run(&args).status.success());
    assert_eq!(fixture.calls().len(), 2);
}

#[test]
fn native_path_tool_is_pinned_even_when_an_override_is_set() {
    let fixture = Fixture::new();
    let native = fixture.0.join("target/bin/cc");
    let override_path = fixture.0.join("target/bin/alternate-cc");
    fs::copy(&native, &override_path).unwrap();
    fs::write(fixture.0.join("target/use-native-tools"), "").unwrap();
    let args = ["--step", "build", "--reuse"];
    success(
        &fixture
            .command(&args)
            .env("CC", &override_path)
            .output()
            .unwrap(),
    );
    let mut bytes = fs::read(&native).unwrap();
    bytes.extend_from_slice(b"\nexit 1\n");
    fs::write(&native, bytes).unwrap();
    assert!(
        !fixture
            .command(&args)
            .env("CC", &override_path)
            .output()
            .unwrap()
            .status
            .success()
    );
}

#[test]
fn a_nonexecutable_path_shadow_cannot_hide_the_compiler_actually_run() {
    let fixture = Fixture::new();
    let shadow = fixture.0.join("target/shadow");
    fs::create_dir(&shadow).unwrap();
    fs::write(shadow.join("cc"), "not executable\n").unwrap();
    let override_path = fixture.0.join("target/bin/alternate-cc");
    fs::copy(fixture.0.join("target/bin/cc"), &override_path).unwrap();
    fs::write(fixture.0.join("target/use-native-tools"), "").unwrap();
    let path = std::env::join_paths([
        shadow,
        fixture.0.join("target/bin"),
        "/usr/bin".into(),
        "/bin".into(),
    ])
    .unwrap();
    let args = ["--step", "build", "--reuse"];
    success(
        &fixture
            .command(&args)
            .env("PATH", &path)
            .env("CC", &override_path)
            .output()
            .unwrap(),
    );
    let native = fixture.0.join("target/bin/cc");
    let mut bytes = fs::read(&native).unwrap();
    bytes.extend_from_slice(b"\nexit 1\n");
    fs::write(native, bytes).unwrap();
    assert!(
        !fixture
            .command(&args)
            .env("PATH", &path)
            .env("CC", &override_path)
            .output()
            .unwrap()
            .status
            .success()
    );
}

#[test]
fn changed_dangling_symlink_identity_invalidates_reuse() {
    let fixture = Fixture::new();
    let link = fixture.0.join("input-link");
    std::os::unix::fs::symlink("missing-first", &link).unwrap();
    assert!(
        Command::new("git")
            .args(["add", "input-link"])
            .current_dir(&fixture.0)
            .status()
            .unwrap()
            .success()
    );
    let args = ["--step", "clippy", "--reuse"];
    success(&fixture.run(&args));
    fs::remove_file(&link).unwrap();
    std::os::unix::fs::symlink("missing-second", &link).unwrap();
    assert!(!fixture.run(&args).status.success());
    assert_eq!(fixture.calls().len(), 2);
}

#[test]
fn rustup_delegated_tool_changes_cannot_hide_behind_an_unchanged_launcher() {
    let fixture = Fixture::new();
    let delegate = fixture.0.join("target/bin/delegated-rustfmt");
    fs::copy(fixture.0.join("target/bin/rustfmt"), &delegate).unwrap();
    let shim = fixture.0.join("target/bin/rustup");
    fs::write(&shim, "#!/bin/sh\nif [ \"$1\" = which ]; then printf '%s/target/bin/delegated-rustfmt\\n' \"$PWD\"; else exec \"$PWD/target/bin/delegated-rustfmt\" \"$@\"; fi\n").unwrap();
    fs::set_permissions(&shim, fs::Permissions::from_mode(0o755)).unwrap();
    fs::remove_file(fixture.0.join("target/bin/rustfmt")).unwrap();
    std::os::unix::fs::symlink(&shim, fixture.0.join("target/bin/rustfmt")).unwrap();
    let args = ["--step", "clippy", "--reuse"];
    success(&fixture.run(&args));
    let mut bytes = fs::read(&delegate).unwrap();
    bytes.extend_from_slice(b"\n# actual formatter changed; launcher/version unchanged\n");
    fs::write(&delegate, bytes).unwrap();
    success(&fixture.run(&args));
    assert_eq!(fixture.calls().len(), 2);
}

#[test]
fn unknown_duplicate_and_missing_stage_arguments_fail_before_running_tools() {
    let fixture = Fixture::new();
    for args in [
        vec!["--step", "unknown"],
        vec!["--step", "clippy", "--step", "clippy"],
        vec!["--step"],
        vec!["--input"],
    ] {
        assert!(!fixture.run(&args).status.success());
    }
    assert!(fixture.calls().is_empty());
}

#[test]
fn input_dump_is_read_only_and_failed_execution_remains_in_the_run_report() {
    let fixture = Fixture::new();
    let command = fixture.command(&[]);
    let input = Command::new(env!("CARGO_BIN_EXE_xtask"))
        .arg("inputs")
        .current_dir(&fixture.0)
        .envs(
            command
                .get_envs()
                .filter_map(|(key, value)| value.map(|value| (key, value))),
        )
        .output()
        .unwrap();
    success(&input);
    let pins: serde_json::Value = serde_json::from_slice(&input.stdout).unwrap();
    assert!(
        pins["files"]
            .as_object()
            .unwrap()
            .contains_key(fixture.0.join("input.rs").to_str().unwrap())
    );
    assert!(fixture.calls().is_empty());
    fs::write(fixture.0.join("target/fail"), "clippy").unwrap();
    let failed = fixture.run(&["--step", "clippy"]);
    assert!(!failed.status.success());
    assert!(String::from_utf8_lossy(&failed.stderr).contains("1 executed"));
    let summary: serde_json::Value = serde_json::from_slice(
        &fs::read(fixture.0.join("target/verification/latest.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(summary["stages"][0]["success"], false);
    assert!(PathBuf::from(summary["stages"][0]["log"].as_str().unwrap()).is_file());
    assert!(summary["stages"][0]["receipt"].is_null());
}
