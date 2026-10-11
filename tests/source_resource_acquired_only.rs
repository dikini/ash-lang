//! Acquired-only reports through public source checking and generated native execution.

use ash::{
    build::{BuildConfiguration, NativeLinkInput, build_prepared, prepare_program},
    driver::{RunConfiguration, compile_path},
    module::ModuleRoots,
};
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, Instant},
};

const OWNER: &str = include_str!("fixtures/source-owner/acquired_only_owner.ash");
const ENTRY: &str = include_str!("fixtures/source-owner/acquired_only_entry.ash");

struct Fixture(PathBuf);
impl Fixture {
    fn new(owner: &str, entry: &str) -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-source-acquired-only-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("owner.ash"), owner).unwrap();
        fs::write(path.join("entry.ash"), entry).unwrap();
        Self(path)
    }
    fn configuration(&self) -> RunConfiguration {
        RunConfiguration {
            entry: self.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        }
    }
    fn run_native(&self) -> (Output, String) {
        let compiled = compile_path(self.configuration()).expect("checked acquired-only resource");
        let native = self.0.join("native_owner.c");
        let object = self.0.join("native_owner.o");
        let archive = self.0.join("libash_owner.a");
        fs::write(
            &native,
            include_str!("fixtures/source-owner/native_owner.c"),
        )
        .unwrap();
        for output in [
            Command::new("cc")
                .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-c"])
                .arg(&native)
                .arg("-o")
                .arg(&object)
                .output()
                .unwrap(),
            Command::new("ar")
                .arg("crs")
                .arg(&archive)
                .arg(&object)
                .output()
                .unwrap(),
        ] {
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        fs::remove_file(self.0.join("entry.ash")).unwrap();
        fs::remove_file(self.0.join("owner.ash")).unwrap();
        let executable = self.0.join("program");
        let mut configuration = BuildConfiguration::new(executable.clone());
        configuration.native_inputs = vec![NativeLinkInput::StaticArchive(archive)];
        let cache = std::env::var_os("CARGO_TARGET_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"));
        configuration.cargo_target_directory = Some(cache.join("ffi-native-hosts"));
        let prepared = prepare_program(&compiled, configuration).unwrap();
        assert!(!prepared.generated_rust().contains("compile_path"));
        if let Err(error) = build_prepared(prepared) {
            let log = error
                .build_log()
                .map(|path| fs::read_to_string(path).unwrap())
                .unwrap_or_default();
            panic!("generated-native build: {error:?}\n{log}");
        }
        let trace = self.0.join("native-trace");
        let mut child = Command::new(executable)
            .env("ASH_OWNER_TRACE", &trace)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let started = Instant::now();
        while child.try_wait().unwrap().is_none() {
            if started.elapsed() > Duration::from_secs(30) {
                child.kill().unwrap();
                let _ = child.wait();
                panic!("acquired-only fixture exceeded its execution deadline");
            }
            thread::sleep(Duration::from_millis(20));
        }
        (
            child.wait_with_output().unwrap(),
            fs::read_to_string(trace).unwrap(),
        )
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn acquired_only_admits_instantiated_roles_without_constructor_name_or_parameter_order_dispatch() {
    for owner in [
        OWNER.to_owned(),
        OWNER
            .replace("Success(T)", "Good(T)")
            .replace("Failure(Unit)", "Bad(Unit)"),
        OWNER
            .replace(
                "Outcome<T> = Success(T)\n    | Failure(Unit)",
                "Outcome<I, T> = Success(T)\n    | Failure(I)",
            )
            .replace("result Outcome<Answer>", "result Outcome<Unit, Answer>"),
    ] {
        let entry = "import owner as Owner\nmain : Unit -> Int\nmain () = 42\n";
        let fixture = Fixture::new(&owner, entry);
        compile_path(fixture.configuration()).expect("exact instantiated constructor roles");
    }
}

#[test]
fn acquired_only_rejects_wrong_constructor_order_payload_or_codec() {
    for owner in [
        OWNER.replace(
            "Success(T)\n    | Failure(Unit)",
            "Failure(Unit)\n    | Success(T)",
        ),
        OWNER.replace("Success(T)", "Success((T, Unit))"),
        OWNER.replace("Failure(Unit)", "Failure(Int)"),
        OWNER.replace("Failure(Unit)", "Failure"),
        OWNER.replace(
            "Success(T)\n    | Failure(Unit)",
            "Success(T)\n    | Failure(Unit)\n    | Other",
        ),
        OWNER.replace("codec acquired_only", "codec scope"),
        OWNER.replace("result Outcome<Answer>", "result Outcome<Unit>"),
    ] {
        let fixture = Fixture::new(&owner, ENTRY);
        let failure = compile_path(fixture.configuration()).expect_err("malformed report codec");
        assert_eq!(failure.reason_code(), "type.argument", "{owner}");
    }
}

#[test]
fn acquired_only_reports_cannot_forge_owner_consumption_or_retention() {
    for owner in [
        OWNER.replace("=> Consumed\n", "=> Retained(state, ())\n"),
        OWNER
            .replace(
                "finish (state, data) => match",
                "finish (state, data) => {\n        let ignored = match",
            )
            .replace(
                "    handlers (state, data)",
                "        Retained(state, ())\n    }\n    handlers (state, data)",
            ),
        OWNER[..OWNER.find("    finish (state, data)").unwrap()].to_owned()
            + "    finish (state, data) => Consumed\n    handlers (state, data) {\n        read () => resume data\n    }\n}\n",
    ] {
        let fixture = Fixture::new(&owner, ENTRY);
        let failure = compile_path(fixture.configuration()).expect_err("forged native disposition");
        assert_eq!(failure.reason_code(), "type.argument", "{owner}");
    }
}

#[test]
fn acquired_only_native_reports_preserve_body_nesting_refusal_and_exact_release() {
    let fixture = Fixture::new(OWNER, ENTRY);
    let (output, trace) = fixture.run_native();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        "(Success(42), Success(8), Failure(()), Failure(()), Success(Success(4)), Success(84), Failure(()))"
    );
    assert_eq!(
        trace,
        "acquire:42\nrelease:42\nacquire:8\nrelease:8\nacquire:0\nacquire:9\nrelease:9\nacquire:64\nacquire:4\nrelease:4\nrelease:64\nacquire:7\nrelease:7\n"
    );
}

#[test]
fn acquired_only_consumed_failure_is_terminal_without_success_or_second_release() {
    let owner = OWNER.replace("=> Consumed\n", "=> ConsumedFailure ()\n");
    let entry = "import owner as Owner\nmain : Unit -> Owner.Outcome<Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    99\n}\n";
    let fixture = Fixture::new(&owner, entry);
    let (output, trace) = fixture.run_native();
    assert!(!output.status.success());
    assert!(
        output.stdout.is_empty(),
        "terminal completion must publish no Success"
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains("source resource completion failed"),
        "{stderr}; native trace: {trace}"
    );
    assert_eq!(trace, "acquire:42\nrelease:42\n");
}
