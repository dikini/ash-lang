//! Unapplied public evidence for the next connected scalar-native build batch.
//! Requires NativeLinkInput and the authenticated Effect-image build path.

use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, Instant},
};

use ash::{
    build::{BuildConfiguration, NativeLinkInput, build_prepared, prepare_program},
    driver::{RunConfiguration, compile_path},
    module::ModuleRoots,
};

const NATIVE: &str = include_str!("fixtures/source-native/native.ash");
const FACADE: &str = include_str!("fixtures/source-native/facade.ash");
const HELPER: &str = include_str!("fixtures/source-native/helper.ash");
const C: &str = include_str!("fixtures/source-native/native_counter.c");

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        loop {
            let id = IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-native-public-e2e-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("native executable fixture: {error}"),
            }
        }
    }

    fn native_inputs(&self) -> [NativeLinkInput; 2] {
        let source = self.0.join("native_counter.c");
        let object = self.0.join("native_counter.o");
        let archive = self.0.join("libash_counter_fixture.a");
        let shared = self.0.join("libash_counter_fixture.so");
        fs::write(&source, C).unwrap();
        checked_tool(
            Command::new("cc")
                .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-fPIC", "-c"])
                .arg(&source)
                .arg("-o")
                .arg(&object),
        );
        checked_tool(Command::new("ar").arg("crs").arg(&archive).arg(&object));
        checked_tool(
            Command::new("cc")
                .args(["-shared", "-Wl,-soname,libash_counter_fixture.so"])
                .arg(&object)
                .arg("-o")
                .arg(&shared),
        );
        [
            NativeLinkInput::StaticArchive(archive),
            NativeLinkInput::SharedLibrary(shared),
        ]
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn checked_tool(command: &mut Command) {
    let output = command
        .output()
        .expect("native fixture tool must be installed");
    assert!(
        output.status.success(),
        "native fixture tool failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

// The test uses the public build phase, with no private image/descriptor edits or
// hand-installed callbacks. Sources disappear before host preparation/linkage.
fn build_case(fixture: &Fixture, name: &str, source: &str, native: NativeLinkInput) -> PathBuf {
    let directory = fixture.0.join(name);
    fs::create_dir(&directory).unwrap();
    for (file, text) in [
        ("entry.ash", source),
        ("native.ash", NATIVE),
        ("facade.ash", FACADE),
        ("helper.ash", HELPER),
    ] {
        fs::write(directory.join(file), text).unwrap();
    }
    let compiled = compile_path(RunConfiguration {
        entry: directory.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .unwrap();
    let compilation_work = *compiled.compilation_work();
    for file in ["entry.ash", "native.ash", "facade.ash", "helper.ash"] {
        fs::remove_file(directory.join(file)).unwrap();
    }
    let mut configuration = BuildConfiguration::new(directory.join("program"));
    configuration.native_inputs = vec![native];
    let cache = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"));
    configuration.cargo_target_directory = Some(cache.join("ffi-native-hosts"));
    let prepared = prepare_program(&compiled, configuration).unwrap();
    assert_eq!(*compiled.compilation_work(), compilation_work);
    assert!(!prepared.generated_rust().contains("compile_path"));
    let preparation_work = prepared.preparation_work();
    drop(compiled);
    let built = build_prepared(prepared).unwrap_or_else(|error| {
        let log = error
            .build_log()
            .and_then(|path| fs::read_to_string(path).ok())
            .unwrap_or_default();
        panic!("{error}\n{log}");
    });
    assert_eq!(built.compilation_work(), compilation_work);
    assert_eq!(built.preparation_work(), preparation_work);
    built.executable().to_path_buf()
}

// LD_LIBRARY_PATH belongs only to this child; no global environment mutation or
// emitted rpath is required. The explicit SONAME makes ordinary lookup observable.
fn run_host(executable: &Path, fixture: &Fixture, supply_loader_path: bool) -> (Output, Vec<u8>) {
    let trace = fixture.0.join("calls.trace");
    fs::write(&trace, []).unwrap();
    let mut command = Command::new(executable);
    if supply_loader_path {
        let mut directories = vec![fixture.0.clone()];
        if let Some(previous) = std::env::var_os("LD_LIBRARY_PATH") {
            directories.extend(std::env::split_paths(&previous));
        }
        command.env(
            "LD_LIBRARY_PATH",
            std::env::join_paths(directories).unwrap(),
        );
    } else {
        command.env_remove("LD_LIBRARY_PATH");
    }
    command
        .current_dir(&fixture.0)
        .env("ASH_NATIVE_COUNTER_TRACE", &trace)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command.spawn().unwrap();
    let started = Instant::now();
    while child.try_wait().unwrap().is_none() {
        if started.elapsed() > Duration::from_secs(30) {
            child.kill().unwrap();
            let _ = child.wait();
            panic!("native fixture child exceeded its 30-second transport deadline");
        }
        thread::sleep(Duration::from_millis(20));
    }
    (child.wait_with_output().unwrap(), fs::read(trace).unwrap())
}

#[test]
fn generated_scalar_hosts_preserve_real_native_counts_and_exact_results_with_both_linkages() {
    let fixture = Fixture::new();
    let inputs = fixture.native_inputs();
    // Keep the whole build matrix sequential: a single root Cargo window owns
    // connected verification. These are real C calls, not corrupted callbacks.
    for (linkage, input) in ["static", "shared"].into_iter().zip(inputs) {
        for (name, source, result, trace) in [
            (
                "success",
                include_str!("fixtures/source-native/cases/success.ash"),
                "127\n",
                b"i".as_slice(),
            ),
            (
                "range-refusal",
                include_str!("fixtures/source-native/cases/range_refusal.ash"),
                "900\n",
                b"".as_slice(),
            ),
            (
                "u64-max",
                include_str!("fixtures/source-native/cases/u64_max.ash"),
                "18446744073709551615\n",
                b"u".as_slice(),
            ),
            (
                "void",
                include_str!("fixtures/source-native/cases/void.ash"),
                "()\n",
                b"v".as_slice(),
            ),
            (
                "imported-repeated",
                include_str!("fixtures/source-native/cases/imported_repeated.ash"),
                "83\n",
                b"ii".as_slice(),
            ),
        ] {
            let executable = build_case(
                &fixture,
                &format!("{linkage}-{name}"),
                source,
                input.clone(),
            );
            if linkage == "shared" && name == "success" {
                let (output, calls) = run_host(&executable, &fixture, false);
                assert!(
                    !output.status.success(),
                    "automatic rpath must not be emitted"
                );
                assert!(output.stdout.is_empty());
                assert!(
                    calls.is_empty(),
                    "loader refusal precedes every native call"
                );
                let diagnostic = String::from_utf8_lossy(&output.stderr);
                assert!(
                    diagnostic.contains("libash_counter_fixture.so"),
                    "{diagnostic}"
                );
                assert!(
                    diagnostic.contains("error while loading shared libraries"),
                    "{diagnostic}"
                );
            }
            // Repeat an independently restored host activation after source loss.
            for _ in 0..2 {
                let (output, calls) = run_host(&executable, &fixture, true);
                assert!(output.status.success(), "{linkage}/{name}: {output:?}");
                assert_eq!(output.stdout, result.as_bytes(), "{linkage}/{name}");
                assert!(output.stderr.is_empty(), "{linkage}/{name}: {output:?}");
                assert_eq!(calls, trace, "{linkage}/{name}: native call count/order");
            }
        }
    }
}
