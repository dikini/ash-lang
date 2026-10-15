//! Registers the copying SQLite experiment and runs an ordinary Ash entry module.

use ash::{
    compiler_work::{CompilationPhase, CompilationWork},
    driver::{RunConfiguration, run_path_with_foreign_runtime},
    foreign::{ForeignRegistrations, provider_manifest, runtime::ForeignRuntime},
    module::{ForeignRegistrationId, ModuleRoots},
};
use ash_foreign_adapter::sqlite_manifest;
use ash_foreign_adapter::{Observations, sqlite_binding};
use std::{error::Error, path::PathBuf, process::ExitCode, sync::Arc};

fn run(entry: PathBuf) -> Result<(), Box<dyn Error>> {
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1))?,
        sqlite_manifest(ForeignRegistrationId::new(2))?,
    ])?;
    let observations = Observations::default();
    let binding = sqlite_binding(
        Arc::clone(
            registrations
                .get("@foreign.sqlite")
                .ok_or("SQLite registration is absent")?,
        ),
        observations.clone(),
    )?;
    let mut runtime = ForeignRuntime::new(vec![binding])?;
    let result = run_path_with_foreign_runtime(
        RunConfiguration {
            entry,
            roots: ModuleRoots::empty().with_foreign_registrations(registrations),
        },
        &mut runtime,
    );
    if let Ok(result) = &result {
        println!("value: {}", result.value_display());
        println!("type: {}", result.type_display());
        print_compilation_work(Some(result.compilation_work()));
    } else if let Err(failure) = &result {
        print_compilation_work(failure.compilation_work());
    }
    for event in observations.events() {
        println!("observation: {event:?}");
    }
    println!("retained owners: {}", runtime.retained_owner_count());
    result?;
    Ok(())
}

fn print_compilation_work(work: Option<&CompilationWork>) {
    let observed = work.copied().unwrap_or_default();
    for (phase, cost) in [
        (CompilationPhase::SourceChecking, observed.source_checking),
        (
            CompilationPhase::FinalElaboration,
            observed.final_elaboration,
        ),
        (CompilationPhase::IndependentCore, observed.independent_core),
    ] {
        if let Some(cost) = cost {
            println!(
                "compiler work: {phase:?} used={} budget={} hard_limit={} completed={} assessment={:?} optimization_target={}",
                cost.used,
                phase.budget(),
                phase.hard_limit(),
                cost.completed,
                cost.assessment(),
                cost.optimization_target(),
            );
        } else {
            println!("compiler work: {phase:?} unobserved");
        }
    }
}

fn main() -> ExitCode {
    let mut arguments = std::env::args_os().skip(1);
    let Some(entry) = arguments.next().filter(|_| arguments.next().is_none()) else {
        eprintln!("usage: sqlite_session <Ash entry path>");
        return ExitCode::from(2);
    };
    match run(PathBuf::from(entry)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("sqlite_session: {error:?}");
            ExitCode::FAILURE
        }
    }
}
