//! Public evidence for compilation versus source-native execution binding.

use ash::{
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

const CONTRACT: &str = r#"import @builtin.foreign as Foreign
pub foreign library C {
    profile "x86_64-unknown-linux-gnu"
    repr CInt = signed(32)
    symbol Abs<Before : EffectRow, T, After : EffectRow> : Int -> Foreign.Call<Int> {
        name "abs"
        abi (CInt) -> CInt
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Stop : Unit -> Foreign.Call<Unit> {
        name "stop"
        abi () -> void
        outcome otherwise {}
    }
}
"#;

#[test]
fn scalar_and_void_source_native_programs_compile_but_default_execution_requires_bindings() {
    for body in [
        "main : Unit -> Foreign.Call<Int> ! {Abs<{}, Int, {}>}\nmain () = perform Abs<{}, Int, {}>.call 1\n",
        "main : Unit -> Foreign.Call<Unit> ! {Stop}\nmain () = perform Stop.call ()\n",
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
        "{CONTRACT}effect Ask {{\n    ask : Unit -> Unit\n}}\nmain : Unit -> Foreign.Call<Int> ! {{Abs<{{}}, Int, {{}}>, Ask}}\nmain () = {{\n    let ignored = perform Ask.ask ()\n    perform Abs<{{}}, Int, {{}}>.call 1\n}}\n"
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
