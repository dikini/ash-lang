use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{
        FileFailure, Observation, PipelineFailure, RunConfiguration, SyntaxFailure, run_path,
    },
    module::{LoadGraphError, ModuleRoots},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempModule(PathBuf);

impl TempModule {
    fn write(name: &str, source: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir().join(format!(
                "ash-integration-module-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let path = directory.join(name);
                    fs::write(&path, source).expect("module fixture should be writable");
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("module fixture directory should be creatable: {error}"),
            }
        }
    }
}

impl Drop for TempModule {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

/// Runs one complete declarations-only module through the public modular driver.
pub fn run_module(name: &str, source: &str) -> Result<Observation, PipelineFailure> {
    let module = TempModule::write(name, source);
    match run_path(RunConfiguration {
        entry: module.0.clone(),
        roots: ModuleRoots::empty(),
    }) {
        Ok(observation) => Ok(observation),
        Err(FileFailure::Pipeline(failure)) => Err(failure),
        Err(FileFailure::Graph(LoadGraphError::Syntax(failure))) => {
            Err(PipelineFailure::Syntax(Box::new(SyntaxFailure {
                lexical: failure.lexical,
                parser: failure.parser,
                resource: failure.resource,
            })))
        }
        Err(FileFailure::Graph(LoadGraphError::Projection { error, .. })) => {
            Err(PipelineFailure::Projection(error))
        }
        Err(FileFailure::Graph(LoadGraphError::SourceModel { error, .. }))
        | Err(FileFailure::Source(error)) => Err(PipelineFailure::SourceModel(error)),
        Err(failure) => panic!("the temporary module fixture reached an input failure: {failure}"),
    }
}
