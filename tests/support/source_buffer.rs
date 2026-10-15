#![allow(dead_code)]

//! Ordinary imported buffer fixtures; execution always uses a generated host.

use ash::{
    build::{BuildConfiguration, build_prepared, prepare_program},
    driver::{FileFailure, RunConfiguration, compile_path},
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

pub fn roots(directory: &Path) -> ModuleRoots {
    fs::write(
        directory.join("native_buffer.ash"),
        include_str!("../../libraries/native_buffer.ash"),
    )
    .unwrap();
    ModuleRoots::new([("ffi", directory)]).unwrap()
}

#[derive(Debug)]
pub struct Observed(String);

impl Observed {
    pub fn value_display(&self) -> String {
        self.0.clone()
    }
    pub fn value(&self) -> &str {
        &self.0
    }
}

struct Fixture(PathBuf);
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

pub fn run_module(name: &str, source: &str) -> Result<Observed, FileFailure> {
    run_modules(name, &[(name, source)])
}

pub fn compile_modules(
    entry: &str,
    modules: &[(&str, &str)],
) -> Result<ash::driver::CompiledProgram, FileFailure> {
    let directory = std::env::temp_dir().join(format!(
        "ash-buffer-compile-{}-{}",
        std::process::id(),
        ash::source::SourceFile::new("buffer", "")
            .unwrap()
            .id()
            .value()
    ));
    fs::create_dir(&directory).unwrap();
    let fixture = Fixture(directory);
    for (name, source) in modules {
        fs::write(fixture.0.join(name), source).unwrap();
    }
    compile_path(RunConfiguration {
        entry: fixture.0.join(entry),
        roots: roots(&fixture.0),
    })
}

pub fn run_modules(entry: &str, modules: &[(&str, &str)]) -> Result<Observed, FileFailure> {
    static IDS: AtomicU64 = AtomicU64::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-migrated-buffer-{}-{}",
        std::process::id(),
        IDS.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let fixture = Fixture(directory);
    for (name, source) in modules {
        fs::write(fixture.0.join(name), source).unwrap();
    }
    let compiled = compile_path(RunConfiguration {
        entry: fixture.0.join(entry),
        roots: roots(&fixture.0),
    })?;
    let executable = fixture.0.join("program");
    let mut configuration = BuildConfiguration::new(executable.clone());
    configuration.cargo_target_directory = Some(
        std::env::var_os("CARGO_TARGET_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
            .join("ffi-native-hosts"),
    );
    let prepared = prepare_program(&compiled, configuration).unwrap();
    println!(
        "normal formula native preparation work: {}",
        prepared.preparation_work()
    );
    for (name, _) in modules {
        fs::remove_file(fixture.0.join(name)).unwrap();
    }
    fs::remove_file(fixture.0.join("native_buffer.ash")).unwrap();
    let built = build_prepared(prepared).unwrap_or_else(|error| {
        let log = error
            .build_log()
            .and_then(|path| fs::read_to_string(path).ok())
            .unwrap_or_default();
        panic!("migrated buffer host: {error:?}\n{log}")
    });
    let generated = built.generated_source().parent().unwrap();
    if let Some(directory) = std::env::var_os("ASH_SQLITE_DIAGNOSTIC_DIR").map(PathBuf::from) {
        fs::create_dir_all(&directory).unwrap();
        for (input, name) in [
            (executable.as_path(), "program"),
            (built.generated_source(), "main.rs"),
            (
                generated.join("program-image.bin").as_path(),
                "program-image.bin",
            ),
            (
                generated.join("expected-facts.bin").as_path(),
                "expected-facts.bin",
            ),
        ] {
            fs::copy(input, directory.join(name)).unwrap();
        }
    }
    fs::remove_file(generated.join("program-image.bin")).unwrap();
    fs::remove_file(generated.join("expected-facts.bin")).unwrap();
    let mut child = Command::new(executable)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let start = Instant::now();
    while child.try_wait().unwrap().is_none() {
        if start.elapsed() > Duration::from_secs(30) {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("migrated buffer host exceeded 30-second execution deadline");
        }
        thread::sleep(Duration::from_millis(20));
    }
    let result = child.wait_with_output().unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    Ok(Observed(
        String::from_utf8(result.stdout).unwrap().trim().to_owned(),
    ))
}
