//! Source-authored arena policy through public compilation and generated hosts.

use ash::{
    build::{BuildConfiguration, NativeLinkInput, build_prepared, prepare_program},
    driver::{PipelineFailure, RunConfiguration, compile_path},
    elaborate::{TypeError, TypeReason},
    module::ModuleRoots,
};
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, Instant},
};

const LIBRARY: &str = include_str!("../libraries/arena.ash");
const ENTRY: &str = include_str!("fixtures/source-arena/entry.ash");
const PRODUCTION_ENTRY: &str = r"import arena as Memory
main : Unit -> Memory.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Int, Int, Int, Int)>
main () = resource Memory.Arena<Fresh> arena = (Memory.ArenaConfig (64, 4)) {
    Memory.usage arena
}
";

struct Fixture(PathBuf);

impl Fixture {
    fn new(library: &str, entry: &str) -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        loop {
            let identity = IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-source-arena-{}-{identity}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => {
                    fs::write(path.join("arena.ash"), library).unwrap();
                    fs::write(path.join("entry.ash"), entry).unwrap();
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("arena fixture directory: {error}"),
            }
        }
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

fn build_configuration(executable: PathBuf) -> BuildConfiguration {
    let mut configuration = BuildConfiguration::new(executable);
    let cache = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"));
    configuration.cargo_target_directory = Some(cache.join("ffi-native-hosts"));
    configuration
}

#[test]
fn production_arena_prepares_direct_calloc_and_free_bridges() {
    let fixture = Fixture::new(LIBRARY, PRODUCTION_ENTRY);
    let compiled = compile_path(fixture.configuration()).expect("source arena admission");
    let prepared = prepare_program(
        &compiled,
        build_configuration(fixture.0.join("production-arena")),
    )
    .expect("production libc bridge preparation");
    let generated = prepared.generated_rust();
    assert!(generated.contains("#[link_name = \"calloc\"]"));
    assert!(generated.contains("#[link_name = \"free\"]"));
    assert!(!generated.contains("ash_arena_calloc"));
    assert!(!generated.contains("ash_arena_free"));
}

#[test]
fn public_arena_rejects_owned_handle_escape() {
    let entry = r"import arena as Memory
main : Unit -> Unit
main () = resource Memory.Arena<Fresh> arena = (Memory.ArenaConfig (64, 4)) {
    arena
}
";
    let fixture = Fixture::new(LIBRARY, entry);
    let failure = compile_path(fixture.configuration()).expect_err("owned handle cannot escape");
    assert!(
        matches!(
            failure.pipeline_failure(),
            Some(PipelineFailure::Typing(TypeError::Source(diagnostic)))
                if diagnostic.reason == TypeReason::ResourceEscape
        ),
        "{failure:?}"
    );
}

fn run_scenario(executable: &Path, fixture: &Fixture, inject: bool) -> (String, String) {
    let scenario = if inject { "injected" } else { "real" };
    let allocator_trace = fixture.0.join(format!("allocator-{scenario}"));
    let input_trace = fixture.0.join(format!("inputs-{scenario}"));
    let mut child = Command::new(executable)
        .env("ASH_ARENA_TRACE", &allocator_trace)
        .env("ASH_ARENA_INPUT_TRACE", &input_trace)
        .env("ASH_ARENA_REFUSE_FIRST", if inject { "1" } else { "0" })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let started = Instant::now();
    while child.try_wait().unwrap().is_none() {
        if started.elapsed() > Duration::from_secs(30) {
            child.kill().unwrap();
            let _ = child.wait();
            panic!("arena {scenario} scenario exceeded its 30-second execution deadline");
        }
        thread::sleep(Duration::from_millis(20));
    }
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "arena {scenario}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        fs::read_to_string(input_trace).unwrap(),
        "negative-one\nminimum-i64\n"
    );
    (
        String::from_utf8(output.stdout).unwrap().trim().to_owned(),
        fs::read_to_string(allocator_trace).unwrap(),
    )
}

#[test]
fn generated_arena_host_checks_preflight_real_backing_and_exact_release() {
    // Change the checked original source before compilation, never its receipts.
    assert_eq!(LIBRARY.matches("name \"calloc\"").count(), 1);
    assert_eq!(LIBRARY.matches("name \"free\"").count(), 1);
    let traced_library = LIBRARY
        .replace("name \"calloc\"", "name \"ash_arena_calloc\"")
        .replace("name \"free\"", "name \"ash_arena_free\"");
    let fixture = Fixture::new(&traced_library, ENTRY);
    let compiled = compile_path(fixture.configuration()).expect("complete arena scenarios");

    let native = fixture.0.join("native_arena.c");
    let object = fixture.0.join("native_arena.o");
    let archive = fixture.0.join("libash_arena_trace.a");
    fs::write(
        &native,
        include_str!("fixtures/source-arena/native_arena.c"),
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

    // One generated host serves both scenarios without source compilation replay.
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    fs::remove_file(fixture.0.join("arena.ash")).unwrap();
    let executable = fixture.0.join("arena-program");
    let mut configuration = build_configuration(executable.clone());
    configuration.native_inputs = vec![NativeLinkInput::StaticArchive(archive)];
    let prepared = prepare_program(&compiled, configuration).unwrap();
    assert!(!prepared.generated_rust().contains("compile_path"));
    build_prepared(prepared).unwrap();

    let observations_after_first = concat!(
        "Observed(0, 0, 0, 0), ",
        "Observed(0, 64, 0, 4), ",
        "Observed(0, 1, 0, 9223372036854775807), ",
        "Invalid, Invalid, Invalid, Invalid, Invalid, Invalid, Invalid, ",
        "Completed(((0, 64, 0, 4), Observed(0, 4, 0, 1)), Closed))"
    );
    let trace_after_first = concat!(
        "calloc:2:1:1\nallocated:2\nfree:2\n",
        "calloc:3:64:1\nallocated:3\nfree:3\n",
        "calloc:4:1:1\nallocated:4\nfree:4\n",
        "calloc:5:64:1\nallocated:5\n",
        "calloc:6:4:1\nallocated:6\nfree:6\nfree:5\n"
    );
    for inject in [false, true] {
        let (observations, trace) = run_scenario(&executable, &fixture, inject);
        let (first_observation, first_trace) = if inject {
            ("AllocationRefused", "injected-refusal:1:64:1\n")
        } else {
            (
                "Observed(0, 64, 0, 4)",
                "calloc:1:64:1\nallocated:1\nfree:1\n",
            )
        };
        assert_eq!(
            observations,
            format!("({first_observation}, {observations_after_first}")
        );
        assert_eq!(trace, format!("{first_trace}{trace_after_first}"));
    }
}

#[test]
fn public_arena_checks_uncertain_scalar_arms_beside_the_current_owner() {
    let finish_start = LIBRARY.find("    finish (state, data) =>").unwrap();
    let finish_end = LIBRARY[finish_start..].find("    handlers ").unwrap() + finish_start;
    let finish = r"    finish (state, data) => match (
        Foreign.checked_i64 (9223372036854775807 + 1),
        state
    ) {
        (Foreign.Returned(_), current) => match perform Free<R>.call current {
            Foreign.Returned(Foreign.Consumed(())) => Consumed
            Foreign.Returned(Foreign.Retained(())) => Retained(current, ReleaseFailed)
            Foreign.Returned(Foreign.BlockedDependent) => Retained(current, ReleaseFailed)
            Foreign.ConversionFailed(_) => Retained(current, ReleaseFailed)
        }
        (Foreign.ConversionFailed(_), _) => Consumed
    }
";
    let mut library = LIBRARY.to_owned();
    library.replace_range(finish_start..finish_end, finish);
    let fixture = Fixture::new(&library, PRODUCTION_ENTRY);
    let failure = compile_path(fixture.configuration())
        .expect_err("the conversion-failure arm cannot report consumption without teardown");
    assert!(
        matches!(
            failure.pipeline_failure(),
            Some(PipelineFailure::Typing(TypeError::Source(diagnostic)))
                if diagnostic.reason == TypeReason::Argument
        ),
        "{failure:?}"
    );
}
