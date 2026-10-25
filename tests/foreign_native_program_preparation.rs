//! Public evidence for compilation versus source-native execution binding.

use ash::{
    build::{BuildConfiguration, prepare_program},
    driver::{EntryReason, PipelineFailure, RunConfiguration, compile_path, execute, run_path},
    eval::RuntimeFailure,
    module::ModuleRoots,
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new(source: &str) -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        loop {
            let id = IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-native-program-preparation-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => {
                    fs::write(path.join("entry.ash"), source).unwrap();
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("native program fixture: {error}"),
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

const CONTRACT: &str = r#"import @builtin.foreign as F
import @builtin.string as T
pub foreign library C {
    profile "x86_64-unknown-linux-gnu"
    symbol Make : Unit -> F.Address { name "fixture_make" }
    symbol Echo : F.Address -> F.Address { name "fixture_echo" }
    symbol Stop : Unit -> Unit { name "fixture_stop" }
    symbol Release : F.Address -> Unit { name "fixture_release" }
    symbol EchoBytes : Bytes -> F.Address { name "fixture_echo_bytes" }
    symbol Pair : (F.Address, Bytes) -> F.Address { name "fixture_pair" }
    symbol Consume : Bytes -> Unit { name "fixture_consume" }
}
"#;

#[test]
fn address_and_void_programs_compile_but_default_execution_requires_bindings() {
    for body in [
        "main : Unit -> F.Address ! {Make}\nmain () = perform Make.call ()\n",
        "main : Unit -> F.Address ! {Echo}\nmain () = perform Echo.call (F.null ())\n",
        "main : Unit -> Unit ! {Stop}\nmain () = perform Stop.call ()\n",
        "main : Unit -> Unit ! {Release}\nmain () = perform Release.call (F.null ())\n",
    ] {
        let fixture = Fixture::new(&format!("{CONTRACT}{body}"));
        let compiled = compile_path(fixture.configuration())
            .expect("native row has an explicit checked Core interpreter");
        let work = *compiled.compilation_work();
        fs::write(fixture.0.join("entry.ash"), "source was replaced\n").unwrap();
        for _ in 0..2 {
            let failure =
                execute(&compiled).expect_err("source authority is not an executable binding");
            assert!(matches!(
                failure.pipeline_failure(),
                Some(PipelineFailure::Runtime(RuntimeFailure::ForeignBinding))
            ));
            assert_eq!(compiled.compilation_work(), &work);
            assert!(failure.sources().is_empty());
        }
        fs::write(fixture.0.join("entry.ash"), format!("{CONTRACT}{body}")).unwrap();
        let failure = run_path(fixture.configuration())
            .expect_err("run_path does not build or link a host implicitly");
        assert!(matches!(
            failure.pipeline_failure(),
            Some(PipelineFailure::Runtime(RuntimeFailure::ForeignBinding))
        ));
    }
}

#[test]
fn native_compilation_discharges_no_ordinary_entry_requirement() {
    let fixture = Fixture::new(&format!(
        "{CONTRACT}effect Ask {{\n    ask : Unit -> Unit\n}}\nmain : Unit -> F.Address ! {{Make, Ask}}\nmain () = {{\n    let ignored = perform Ask.ask ()\n    perform Make.call ()\n}}\n"
    ));
    for failure in [
        compile_path(fixture.configuration()).unwrap_err(),
        run_path(fixture.configuration()).unwrap_err(),
    ] {
        assert!(
            matches!(failure.pipeline_failure(), Some(PipelineFailure::Entry(entry)) if entry.reason() == EntryReason::MainEffects)
        );
    }
}

#[test]
fn passive_native_declarations_keep_default_execution_available() {
    let fixture = Fixture::new(&format!("{CONTRACT}main : Unit -> Int\nmain () = 42\n"));
    let compiled = compile_path(fixture.configuration()).unwrap();
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
    assert_eq!(
        run_path(fixture.configuration()).unwrap().value_display(),
        "42"
    );
}

#[test]
fn native_preparation_preserves_core_row_metadata_depth() {
    // The ordinary handler and its executed request carry the nested row into
    // typed Core. Foreign symbols themselves have no type or row parameters.
    let template = include_str!("fixtures/source-native/cases/deep-rows.ash");
    assert_eq!(template.matches("DEEP_ROW").count(), 2);
    for nesting in [42, 43] {
        let mut row = "{}".to_owned();
        for _ in 0..nesting {
            row = format!("{{Nest<{row}>}}");
        }
        let source = template.replace("DEEP_ROW", &row);
        let fixture = Fixture::new(&source);
        fs::write(
            fixture.0.join("native.ash"),
            include_str!("fixtures/source-native/native.ash"),
        )
        .unwrap();
        let compiled = compile_path(fixture.configuration()).unwrap_or_else(|failure| {
            panic!("{nesting} ordinary nested rows must compile: {failure}")
        });
        let compilation_work = *compiled.compilation_work();
        fs::remove_file(fixture.0.join("entry.ash")).unwrap();
        fs::remove_file(fixture.0.join("native.ash")).unwrap();
        // Both admitted depths remain positive normal-preparation regressions.
        let prepared = prepare_program(
            &compiled,
            BuildConfiguration::new(fixture.0.join("program")),
        )
        .unwrap_or_else(|failure| panic!("{nesting} admitted nested rows: {failure}"));
        assert!(prepared.preparation_work() > 0);
        assert_eq!(*compiled.compilation_work(), compilation_work);
    }
}

#[test]
fn bytes_and_flat_pointer_arguments_reach_normal_native_preparation() {
    for body in [
        "main : Unit -> F.Address ! {EchoBytes}\nmain () = perform EchoBytes.call (T.to_utf8 \"abc\")\n",
        "main : Unit -> F.Address ! {Pair}\nmain () = perform Pair.call (F.null (), T.to_utf8 \"abc\")\n",
        "main : Unit -> Unit ! {Consume}\nmain () = perform Consume.call (T.to_utf8 \"abc\")\n",
    ] {
        let fixture = Fixture::new(&format!("{CONTRACT}{body}"));
        let compiled = compile_path(fixture.configuration()).unwrap();
        let compilation_work = *compiled.compilation_work();
        fs::remove_file(fixture.0.join("entry.ash")).unwrap();
        let prepared = prepare_program(
            &compiled,
            BuildConfiguration::new(fixture.0.join("program")),
        )
        .unwrap();
        assert!(prepared.preparation_work() > 0);
        assert_eq!(*compiled.compilation_work(), compilation_work);
    }
}
