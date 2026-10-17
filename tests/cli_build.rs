use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new(source: &str) -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash cli native inputs {} {}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("entry.ash"), source).unwrap();
        Self(path)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn checked_tool(command: &mut Command) {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn native_host_cache(directory: Option<PathBuf>) -> PathBuf {
    directory
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
        .join("ffi-native-hosts")
}

#[test]
fn native_host_cache_uses_the_override_or_repository_default() {
    assert_eq!(
        native_host_cache(None),
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("target")
            .join("ffi-native-hosts")
    );
    assert_eq!(
        native_host_cache(Some(PathBuf::from("cache with spaces"))),
        PathBuf::from("cache with spaces").join("ffi-native-hosts")
    );
}

#[test]
fn cli_links_distinct_static_shared_dependencies_and_preserves_output_on_link_refusal() {
    let fixture = Fixture::new(
        r#"import @builtin.foreign as Foreign
foreign library Native {
    profile "x86_64-unknown-linux-gnu"
    repr CInt = signed(32)
    symbol Entry : Int -> Foreign.Call<Int> {
        name "ash_cli_entry"
        abi (CInt) -> CInt
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
main : Unit -> Int ! {Entry}
main () = match perform Entry.call 40 {
    Foreign.Returned(value) => value
    Foreign.ConversionFailed(_) => 0
}
"#,
    );
    for (name, code) in [
        (
            "first",
            "extern int ash_cli_middle(int); int ash_cli_entry(int value) { return ash_cli_middle(value) + 1; }\n",
        ),
        (
            "middle",
            "extern int ash_cli_last(int); int ash_cli_middle(int value) { return ash_cli_last(value) + 1; }\n",
        ),
        ("last", "int ash_cli_last(int value) { return value; }\n"),
    ] {
        let source = fixture.0.join(format!("{name}.c"));
        fs::write(&source, code).unwrap();
        checked_tool(
            Command::new("cc")
                .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-fPIC", "-c"])
                .arg(source)
                .arg("-o")
                .arg(fixture.0.join(format!("{name}.o"))),
        );
    }
    for name in ["first", "last"] {
        checked_tool(
            Command::new("ar")
                .arg("crs")
                .arg(fixture.0.join(format!("lib{name} input.a")))
                .arg(fixture.0.join(format!("{name}.o"))),
        );
    }
    let shared = fixture.0.join("libash_cli_middle.so");
    checked_tool(
        Command::new("cc")
            .args(["-shared", "-Wl,-soname,libash_cli_middle.so"])
            .arg(fixture.0.join("middle.o"))
            .arg("-o")
            .arg(&shared),
    );
    let executable = fixture.0.join("linked program");
    fs::write(&executable, "existing program").unwrap();
    let cache = native_host_cache(std::env::var_os("CARGO_TARGET_DIR").map(PathBuf::from));
    // First -> middle -> last is a real dependency chain with unique symbols.
    // Omitting last must fail at linkage without publishing over the old file.
    for complete in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_ash"));
        command
            .args(["--message-format", "json", "build", "--output"])
            .arg(&executable)
            .arg("--cargo-target-dir")
            .arg(&cache)
            .arg("--native-static")
            .arg(fixture.0.join("libfirst input.a"))
            .arg("--native-shared")
            .arg(&shared);
        if complete {
            command
                .arg("--native-static")
                .arg(fixture.0.join("liblast input.a"));
        }
        let output = command.arg(fixture.0.join("entry.ash")).output().unwrap();
        if complete {
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(
                PathBuf::from(String::from_utf8(output.stdout).unwrap().trim()),
                executable
            );
            assert!(output.stderr.is_empty());
        } else {
            assert_eq!(output.status.code(), Some(2));
            let diagnostic: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
            assert_eq!(diagnostic["reason"], "build.native-tool");
            assert_eq!(fs::read_to_string(&executable).unwrap(), "existing program");
        }
    }
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    let output = Command::new(&executable)
        .env("LD_LIBRARY_PATH", &fixture.0)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"42\n");
    assert!(output.stderr.is_empty());
    println!(
        "CLI mixed static/shared host returned42 after source removal; missing-last link refused and preserved existing destination"
    );
}

#[test]
fn native_input_refusals_keep_build_diagnostics_and_the_existing_destination() {
    let fixture = Fixture::new("main : Unit -> Int\nmain () = 7\n");
    let destination = fixture.0.join("program");
    fs::write(&destination, "existing program").unwrap();
    for flag in ["--native-static", "--native-shared"] {
        for (path, reason) in [
            (fixture.0.join("entry.ash"), "build.native-input"),
            (fixture.0.join("missing library"), "build.input-output"),
        ] {
            let output = Command::new(env!("CARGO_BIN_EXE_ash"))
                .args(["--message-format", "json", "build", "--output"])
                .arg(&destination)
                .arg(flag)
                .arg(path)
                .arg(fixture.0.join("entry.ash"))
                .output()
                .unwrap();
            assert_eq!(output.status.code(), Some(2));
            assert!(output.stdout.is_empty());
            let diagnostic: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
            assert_eq!(diagnostic["reason"], reason);
            assert_eq!(
                fs::read_to_string(&destination).unwrap(),
                "existing program"
            );
        }
    }
}

#[test]
fn build_invocation_preserves_source_diagnostics_without_linking() {
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .args([
            "build",
            "--message-format",
            "json",
            "--output",
            "unused-program",
            "/nonexistent/ash-build-entry.ash",
        ])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let diagnostic: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
    assert_eq!(diagnostic["reason"], "input.read");
}

#[test]
fn build_invocation_reports_preparation_refusal_in_the_selected_format() {
    let entry = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/first-stratum/valid/v001-precedence.ash");
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .args([
            "--message-format",
            "json",
            "build",
            "--output",
            "unused-program",
            "--target",
            "unsupported-profile",
        ])
        .arg(entry)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let diagnostic: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
    assert_eq!(diagnostic["reason"], "build.unsupported-target");
    assert_eq!(diagnostic["responsibility"], "invocation");
}

#[test]
fn build_invocation_requires_one_output_and_options_before_the_entry() {
    for arguments in [
        vec!["build", "entry.ash"],
        vec!["build", "--output", "one", "--output", "two", "entry.ash"],
        vec!["build", "entry.ash", "--output", "program"],
        vec!["build", "--output", "program", "--native-static"],
        vec!["build", "--output", "program", "--native-shared"],
        vec![
            "build",
            "--output",
            "program",
            "entry.ash",
            "--native-static",
            "lib.a",
        ],
        vec![
            "build",
            "--output",
            "program",
            "entry.ash",
            "--native-shared",
            "lib.so",
        ],
        vec![
            "build",
            "--output",
            "program",
            "--native-static=lib.a",
            "entry.ash",
        ],
        vec!["--native-static", "lib.a", "entry.ash"],
        vec!["--native-shared", "lib.so", "entry.ash"],
        vec!["check-ffi", "--native-static", "lib.a", "entry.ash"],
        vec!["check-ffi", "--native-shared", "lib.so", "entry.ash"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_ash"))
            .args(["--message-format", "json"])
            .args(arguments)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        let diagnostic: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
        assert_eq!(diagnostic["reason"], "invocation.usage");
    }
}
