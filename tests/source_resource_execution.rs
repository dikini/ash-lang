//! Product resource admission and real native calls through the public build.

use ash::{
    build::{BuildConfiguration, NativeLinkInput, build_prepared, prepare_program},
    driver::{RunConfiguration, compile_path},
    module::ModuleRoots,
};
use std::{
    fs,
    path::PathBuf,
    process::{Command, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, Instant},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new(entry: &str) -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-source-owner-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(
            path.join("owner.ash"),
            include_str!("fixtures/source-owner/owner.ash"),
        )
        .unwrap();
        fs::write(path.join("entry.ash"), entry).unwrap();
        Self(path)
    }
    fn configuration(&self) -> RunConfiguration {
        RunConfiguration {
            entry: self.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        }
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn source_resource_lifecycle_compiles_from_original_checked_templates() {
    let fixture = Fixture::new(include_str!("fixtures/source-owner/entry.ash"));
    let compiled =
        compile_path(fixture.configuration()).expect("complete source owner/resource admission");
    println!(
        "source owner compilation work: {:?}",
        compiled.compilation_work()
    );
}

#[test]
fn generated_owner_host_acquires_publishes_private_payload_and_releases_once() {
    generated_owner_case(include_str!("fixtures/source-owner/owner.ash"));
}

#[test]
fn generated_initialized_byte_owner_host_preserves_native_acquisition_and_release() {
    // The native fixture initializes one eight-byte size_t object. Seven bytes
    // therefore form a valid promised region, independent of its stored value.
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("repr Address = opaque", "repr Address = bytes")
        .replace(
            ": Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
            ": (Int, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
        )
        .replace(
            "outcome result nonnull { readable result }",
            "outcome result nonnull { readable result, initialized_bytes result from 1 }",
        )
        .replace(".call size {", ".call (size, 7) {");
    generated_owner_case(&owner);
    // A zero initialized extent still owns a non-null native allocation.
    generated_owner_case(&owner.replace(".call (size, 7) {", ".call (size, 0) {"));
}

#[test]
fn initialized_byte_resource_without_initialization_fact_is_rejected() {
    let fixture = Fixture::new(include_str!("fixtures/source-owner/entry.ash"));
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("repr Address = opaque", "repr Address = bytes");
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    let failure = compile_path(fixture.configuration()).unwrap_err();
    assert_eq!(failure.reason_code(), "foreign.contract");
}

#[test]
fn generated_initialized_byte_extents_refuse_before_native_owner_entry() {
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("repr Address = opaque", "repr Address = bytes")
        .replace(
            ": Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
            ": (Int, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
        )
        .replace(
            "outcome result nonnull { readable result }",
            "outcome result nonnull { readable result, initialized_bytes result from 1 }",
        )
        .replace("input Int", "input (Int, Int)")
        .replace("acquire size =>", "acquire (size, extent) =>")
        .replace(".call size {", ".call (size, extent) {");
    let entry = r#"import @builtin.foreign as Foreign
import owner as Owner
foreign library Inputs {
    profile "x86_64-unknown-linux-gnu"
    repr Signed = signed(64)
    symbol NegativeInput : Unit -> Foreign.Call<Int> {
        name "ash_owner_negative_input"
        abi () -> Signed
        output result as scalar
        outcome otherwise { readable result }
    }
}
unreachable : Unit -> Int
unreachable () = unreachable ()
probe : Int -> Owner.Scope<Unit, Unit, Int>
probe extent = resource Owner.Probe<{}, Fresh, {}> owner = (42, extent) {
    unreachable ()
}
main : Unit -> (Owner.Scope<Unit, Unit, Int>, Owner.Scope<Unit, Unit, Int>) ! {NegativeInput}
main () = {
    let negative = match perform NegativeInput.call () {
        Foreign.Returned(value) => value
        Foreign.ConversionFailed(_) => 0
    }
    (probe negative, probe ((9223372036854775807 + 1) * 2))
}
"#;
    generated_owner_program(&owner, entry, "(NotAcquired(()), NotAcquired(()))", "");
}

fn generated_owner_case(owner: &str) {
    generated_owner_program(
        owner,
        include_str!("fixtures/source-owner/entry.ash"),
        "(Completed(42, Closed), Completed(8, Closed), NotAcquired(()), NotAcquired(()), Completed(Completed(4, Closed), Closed), Completed(84, Closed), NotAcquired(()))",
        "acquire:42\nrelease:42\nacquire:8\nrelease:8\nacquire:0\nacquire:9\nrelease:9\nacquire:64\nacquire:4\nrelease:4\nrelease:64\nacquire:7\nrelease:7\n",
    );
}

fn generated_owner_program(owner: &str, entry: &str, expected_result: &str, expected_trace: &str) {
    let fixture = Fixture::new(entry);
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    let compiled = compile_path(fixture.configuration()).unwrap();
    let native = fixture.0.join("native_owner.c");
    let object = fixture.0.join("native_owner.o");
    let archive = fixture.0.join("libash_owner.a");
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
    // The generated host restores checked Core; it does not reopen Ash source.
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    fs::remove_file(fixture.0.join("owner.ash")).unwrap();
    let executable = fixture.0.join("program");
    let mut configuration = BuildConfiguration::new(executable.clone());
    configuration.native_inputs = vec![NativeLinkInput::StaticArchive(archive)];
    let cache = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"));
    configuration.cargo_target_directory = Some(cache.join("ffi-native-hosts"));
    let prepared = prepare_program(&compiled, configuration).unwrap();
    assert!(!prepared.generated_rust().contains("compile_path"));
    build_prepared(prepared).unwrap();
    let trace = fixture.0.join("native-trace");
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
            panic!("owner fixture exceeded its 30-second execution deadline");
        }
        thread::sleep(Duration::from_millis(20));
    }
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        expected_result
    );
    if expected_trace.is_empty() {
        assert!(
            !trace.exists(),
            "refused extents must not enter native owner code"
        );
    } else {
        assert_eq!(fs::read_to_string(trace).unwrap(), expected_trace);
    }
}
