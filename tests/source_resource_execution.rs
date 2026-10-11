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
    let fixture = Fixture::new(include_str!("fixtures/source-owner/entry.ash"));
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
        "(Completed(42, Closed), Completed(8, Closed), NotAcquired(()), NotAcquired(()), Completed(Completed(4, Closed), Closed), Completed(84, Closed), NotAcquired(()))"
    );
    assert_eq!(
        fs::read_to_string(trace).unwrap(),
        "acquire:42\nrelease:42\nacquire:8\nrelease:8\nacquire:0\nacquire:9\nrelease:9\nacquire:64\nacquire:4\nrelease:4\nrelease:64\nacquire:7\nrelease:7\n"
    );
}
