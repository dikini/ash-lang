#![allow(
    dead_code,
    reason = "integration binaries use different subsets of this shared fixture harness"
)]

use ash::{
    driver::{RunConfiguration, run_path_with_foreign_runtime},
    foreign::{ForeignRegistrations, provider_manifest, runtime::ForeignRuntime, sqlite_manifest},
    module::{ForeignRegistrationId, ModuleRoots},
};
use ash_foreign_adapter::{Event, Observations, sqlite_binding};
use std::{
    fs,
    path::PathBuf,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

static NEXT_FIXTURE: AtomicUsize = AtomicUsize::new(0);

pub struct Fixture(PathBuf);
impl Fixture {
    pub fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
    pub fn new() -> Self {
        let directory = std::env::temp_dir().join(format!(
            "ash-sqlite-copying-{}-{}",
            std::process::id(),
            NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let source = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/provider-experiments/sqlite-copying");
        for entry in fs::read_dir(source).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|extension| extension == "ash") {
                fs::copy(&path, directory.join(path.file_name().unwrap())).unwrap();
            }
        }
        Self(directory)
    }
    pub fn run(&self, name: &str) -> (String, Observations) {
        let registrations = ForeignRegistrations::new([
            provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
            sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
        ])
        .unwrap();
        let observations = Observations::default();
        let binding = sqlite_binding(
            Arc::clone(registrations.get("@foreign.sqlite").unwrap()),
            observations.clone(),
        )
        .unwrap();
        let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
        let result = run_path_with_foreign_runtime(
            RunConfiguration {
                entry: self.0.join(name),
                roots: ModuleRoots::empty().with_foreign_registrations(registrations),
            },
            &mut runtime,
        )
        .unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
        assert_eq!(runtime.retained_owner_count(), 0, "{name}");
        assert!(
            !observations
                .events()
                .iter()
                .any(|event| matches!(event, Event::FaultInjected { .. }))
        );
        (result.value_display().to_owned(), observations)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

pub fn copied_sizes(observations: &Observations) -> (Vec<usize>, Vec<usize>) {
    let mut input = Vec::new();
    let mut output = Vec::new();
    for event in observations.events() {
        match event {
            Event::InputCopied(size) => input.push(size),
            Event::OutputCopied(size) => output.push(size),
            _ => {}
        }
    }
    (input, output)
}

pub fn scope_failure(category: &str, reason: &str) -> String {
    format!("Completed(Completed(Err(ForeignError({category}({reason}))), Closed), Closed)")
}

pub fn probe(fixture: &Fixture, sql: &str, body: &str) -> (String, Observations) {
    let source = format!(
        r#"import provider as Provider
import sqlite as Sqlite
import @builtin.bytes as B
main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Unit>>>
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {{
resource Sqlite.Statement<S> stmt = (db, Sqlite.SqlText {sql:?}) {{
{body}
}}
}}
discard_result<T> : Sqlite.Result<T> -> Sqlite.Result<Unit>
discard_result result = match result {{
Sqlite.Ok(value) => Sqlite.Ok ()
Sqlite.Err(error) => Sqlite.Err error
}}
step_result : Sqlite.StepResult -> Sqlite.Result<Unit>
step_result result = match result {{
Sqlite.Row => Sqlite.Ok ()
Sqlite.Done => Sqlite.Ok ()
Sqlite.StepError(error) => Sqlite.Err error
}}
"#
    );
    fs::write(fixture.0.join("probe.ash"), source).unwrap();
    fixture.run("probe.ash")
}

pub fn in_row(body: &str) -> String {
    format!(
        "match Sqlite.step stmt {{\nSqlite.Row => {body}\nSqlite.Done => Sqlite.Err Sqlite.MissingRow\nSqlite.StepError(error) => Sqlite.Err error\n}}"
    )
}

pub fn assert_finish_dispatches(
    observations: &Observations,
    statements: usize,
    connections: usize,
) {
    let events = observations.events();
    for (operation, count) in [("finalize", statements), ("close", connections)] {
        let dispatches: Vec<_> = events
            .iter()
            .enumerate()
            .filter_map(|(index, event)| {
                matches!(event, Event::FinishDispatched { operation: name } if *name == operation)
                    .then_some(index)
            })
            .collect();
        let native_calls: Vec<_> = events
            .iter()
            .enumerate()
            .filter_map(|(index, event)| {
                matches!(event, Event::Call { operation: name, .. } if *name == operation)
                    .then_some(index)
            })
            .collect();
        assert_eq!(dispatches.len(), count, "source finish {operation}");
        assert_eq!(native_calls.len(), count, "native finish {operation}");
        for (dispatch, native_call) in dispatches.iter().zip(native_calls.iter()) {
            assert!(dispatch < native_call, "finish dispatch before {operation}");
        }
    }
}

pub fn assert_closed_probe(observations: &Observations, steps: usize) {
    for (operation, count) in [
        ("open", 1),
        ("prepare", 1),
        ("step", steps),
        ("finalize", 1),
        ("close", 1),
    ] {
        assert_eq!(observations.calls(operation), count, "{operation}");
    }
    assert_finish_dispatches(observations, 1, 1);
    let events = observations.events();
    let finalize = events
        .iter()
        .position(|event| {
            matches!(
                event,
                Event::Call {
                    operation: "finalize",
                    ..
                }
            )
        })
        .unwrap();
    let close_dispatch = events
        .iter()
        .position(|event| matches!(event, Event::FinishDispatched { operation: "close" }))
        .unwrap();
    assert!(
        finalize < close_dispatch,
        "statement completes before connection finish dispatch"
    );
}
