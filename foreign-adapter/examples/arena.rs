//! Host registration and execution for the bounded arena experiment.
//!
//! Supply an Ash entry path. Static manifests are paired with executable native
//! bindings; native observations remain available after source completion.

use ash::{
    driver::{RunConfiguration, run_path_with_foreign_runtime},
    foreign::{ForeignRegistrations, arena_manifest, provider_manifest, runtime::ForeignRuntime},
    module::{ForeignRegistrationId, ModuleRoots},
};
use ash_foreign_adapter::{ArenaObservations, arena_binding};
use std::{error::Error, io, path::PathBuf, sync::Arc};

fn main() -> Result<(), Box<dyn Error>> {
    let mut arguments = std::env::args_os().skip(1);
    let entry = arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "usage: arena <entry.ash>"))?;
    if arguments.next().is_some() {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, "usage: arena <entry.ash>").into());
    }
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1))?,
        arena_manifest(ForeignRegistrationId::new(2))?,
    ])?;
    let observations = ArenaObservations::default();
    let manifest = registrations.get("@foreign.memory").ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            "arena manifest registration absent",
        )
    })?;
    let binding = arena_binding(Arc::clone(manifest), observations.clone())?;
    let mut runtime = ForeignRuntime::new(vec![binding])?;
    let result = run_path_with_foreign_runtime(
        RunConfiguration {
            entry,
            roots: ModuleRoots::empty().with_foreign_registrations(registrations),
        },
        &mut runtime,
    );
    for event in observations.events() {
        eprintln!("{event:?}");
    }
    println!("{}", result?.value_display());
    Ok(())
}
