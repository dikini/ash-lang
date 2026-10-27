use std::{
    fs,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    build::{BuildConfiguration, build_prepared, prepare_program},
    driver::{RunConfiguration, compile_path},
    module::ModuleRoots,
};

static IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);
impl Fixture {
    fn new(source: &str) -> Self {
        loop {
            let id = IDS.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("ash-program-build-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => {
                    fs::write(path.join("entry.ash"), source).unwrap();
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("program build fixture: {error}"),
            }
        }
    }

    fn source(&self) -> RunConfiguration {
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
fn generated_executable_runs_imported_core_after_the_original_source_graph_disappears() {
    let fixture = Fixture::new(
        "import dependency as Dep\nextract : Dep.Count -> Int\nextract value = match value {\n    Dep.Count(payload) => payload + 1\n}\nmain : Unit -> Int\nmain () = extract (Dep.Count(41))\n",
    );
    fs::write(
        fixture.0.join("dependency.ash"),
        "pub type Count = Count(Int)\n",
    )
    .unwrap();
    let checked = compile_path(fixture.source()).unwrap();
    let source_work = *checked.compilation_work();
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    fs::remove_file(fixture.0.join("dependency.ash")).unwrap();
    let mut configuration = BuildConfiguration::new(fixture.0.join("program"));
    let cache = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"));
    configuration.cargo_target_directory = Some(cache.join("ffi-native-hosts"));
    let prepared = prepare_program(&checked, configuration).unwrap();
    assert!(prepared.preparation_work() > 0);
    assert!(
        prepared
            .generated_rust()
            .contains("__run_private_effect_image")
    );
    assert!(!prepared.generated_rust().contains("compile_path"));
    let prepared_work = prepared.preparation_work();
    assert_eq!(*checked.compilation_work(), source_work);
    drop(checked);
    let built = build_prepared(prepared).unwrap_or_else(|error| {
        let log = error
            .build_log()
            .and_then(|path| fs::read_to_string(path).ok())
            .unwrap_or_default();
        panic!("{error}\n{log}");
    });
    assert_eq!(built.compilation_work(), source_work);
    assert_eq!(built.preparation_work(), prepared_work);
    assert!(built.generated_source().is_file());
    assert!(built.build_log().is_file());
    for _ in 0..2 {
        let output = Command::new(built.executable())
            .current_dir(&fixture.0)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, b"42\n");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn pure_generated_host_restores_reexported_string_intrinsics_without_native_links() {
    let fixture = Fixture::new(
        r#"import facade as Text

main : Unit -> (Int, Bool)
main () = match Text.decode (Text.encode "é") {
    Text.Decoded(copied) => (Text.byte_length copied, Text.equal (copied, "é"))
    Text.InvalidUtf8 => (999, false)
}
"#,
    );
    fs::write(
        fixture.0.join("facade.ash"),
        "pub import @builtin.string (to_utf8 as encode, from_utf8 as decode, byte_length, equal, Decoded, InvalidUtf8)\n",
    )
    .unwrap();
    let checked = compile_path(fixture.source()).expect("pure string intrinsic facade admission");
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    fs::remove_file(fixture.0.join("facade.ash")).unwrap();
    let mut configuration = BuildConfiguration::new(fixture.0.join("string-intrinsics"));
    let cache = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"));
    configuration.cargo_target_directory = Some(cache.join("ffi-native-hosts"));
    let prepared = prepare_program(&checked, configuration).expect("pure string image preparation");
    assert!(
        prepared
            .generated_rust()
            .contains("__run_private_effect_image")
    );
    assert!(!prepared.generated_rust().contains("compile_path"));
    assert!(!prepared.generated_rust().contains("#[link_name"));
    drop(checked);
    let built = build_prepared(prepared).unwrap_or_else(|error| {
        let log = error
            .build_log()
            .and_then(|path| fs::read_to_string(path).ok())
            .unwrap_or_default();
        panic!("{error}\n{log}");
    });
    // A linked host needs neither source nor generated construction inputs.
    let generated = built.generated_source();
    for name in ["program-image.bin", "expected-facts.bin"] {
        let path = generated.parent().unwrap().join(name);
        if path.exists() {
            fs::remove_file(path).unwrap();
        }
    }
    fs::remove_file(generated).unwrap();
    let output = Command::new(built.executable())
        .current_dir(&fixture.0)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"(2, true)\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn build_preparation_rejects_unsupported_targets_and_metadata_without_native_tools() {
    let fixture = Fixture::new("type Generic<T> = Generic(T)\nmain : Unit -> Int\nmain () = 42\n");
    let checked = compile_path(fixture.source()).unwrap();
    let mut configuration = BuildConfiguration::new(fixture.0.join("program"));
    configuration.target = "unsupported-profile".to_owned();
    assert!(
        prepare_program(&checked, configuration)
            .unwrap_err()
            .to_string()
            .contains("matching host")
    );
    assert!(!fixture.0.join(".ash-build").exists());
    assert!(!fixture.0.join("program").exists());
    // The Source program now uses Effect Core, whose image admits this metadata.
    // The deliberate Pure RegistryMetadata refusal remains in the existing
    // build::image::tests::unsupported_registry_facts_are_refused_instead_of_dropped.
    let prepared = prepare_program(&checked, BuildConfiguration::new(fixture.0.join("program")))
        .expect("the unchanged Source metadata is supported by its Effect image");
    assert!(
        prepared
            .generated_rust()
            .contains("__run_private_effect_image")
    );
}

#[test]
fn private_runtime_refuses_a_mismatched_compiler_before_decoding() {
    let failure = ash::build::__run_private_pure_image(&[0; 32], b"malformed image").unwrap_err();
    assert_eq!(
        failure.to_string(),
        "embedded program requires its matching compiler/runtime"
    );
}

#[test]
fn generated_generic_cell_host_preserves_function_snapshot_after_source_removal() {
    let fixture = Fixture::new(
        "import @builtin.generic_cell as Cell\nindependent : Unit -> Int\nindependent () = 7\nreplacement : Unit -> Int\nreplacement () = 42\nmain : Unit -> Int\nmain () = {\nlet saved = resource Cell.Cell<R,(Unit -> Int)> c = independent {\nlet old = Cell.read c\nlet _ = Cell.write (c,replacement)\nold\n}\nsaved ()\n}\n",
    );
    let checked = compile_path(fixture.source()).unwrap();
    let mut configuration = BuildConfiguration::new(fixture.0.join("generic-program"));
    let cache = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"));
    configuration.cargo_target_directory = Some(cache.join("ffi-native-hosts"));
    let prepared = prepare_program(&checked, configuration).unwrap();
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    drop(checked);
    let built = build_prepared(prepared).unwrap_or_else(|error| {
        let log = error
            .build_log()
            .and_then(|path| fs::read_to_string(path).ok())
            .unwrap_or_default();
        panic!("{error}\n{log}");
    });
    for _ in 0..2 {
        let output = Command::new(built.executable())
            .current_dir(&fixture.0)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, b"7\n");
        assert!(output.stderr.is_empty());
    }
}
