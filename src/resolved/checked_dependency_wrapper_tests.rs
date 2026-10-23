//! Combined dependent-owner facade correspondence, without runtime execution.

use super::*;
use crate::{
    module::{ModuleGraph, ModuleRoots},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason},
};
use std::sync::atomic::{AtomicU64, Ordering};

fn facade_graph(source: &str) -> ModuleGraph {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    struct Fixture(std::path::PathBuf);
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let fixture = loop {
        let path = std::env::temp_dir().join(format!(
            "ash-dependent-facade-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        match std::fs::create_dir(&path) {
            Ok(()) => break Fixture(path),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("create owned facade fixture: {error}"),
        }
    };
    std::fs::write(fixture.0.join("producer.ash"), source).unwrap();
    std::fs::write(
        fixture.0.join("facade.ash"),
        "pub import producer (run as closed)\n",
    )
    .unwrap();
    std::fs::write(
        fixture.0.join("entry.ash"),
        "import @builtin.foreign as Foreign\nimport facade (closed)\nmain : Unit -> Foreign.CheckedScope<Foreign.CheckedScope<Int, Unit, Unit>, Unit, Unit>\nmain () = closed ()\n",
    )
    .unwrap();
    crate::module::load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty()).unwrap()
}

fn resolve_consumer(
    graph: &ModuleGraph,
    summaries: &[ExportSummary],
) -> Result<ResolvedModule, ResolveModuleError> {
    let entry = graph
        .modules()
        .iter()
        .find(|loaded| loaded.id() == graph.entry())
        .unwrap();
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| {
            DependencyExports::new(
                edge,
                summaries
                    .iter()
                    .find(|summary| summary.module == edge.target())
                    .unwrap(),
            )
            .unwrap()
        })
        .collect::<Vec<_>>();
    crate::resolve::resolve_checked_foreign_module(entry, &dependencies)
}

pub(super) fn assert_body_free_dependent_facade(source: &str) {
    let graph = facade_graph(source);
    let checked = super::checked_hidden_provider_interface_tests::check_graph(&graph)
        .expect("real dependent producer, renamed facade and consumer check canonically");
    let mut summaries = checked
        .into_iter()
        .map(CheckedModule::into_exports)
        .collect::<Vec<_>>();
    let module = |name: &str| {
        graph
            .modules()
            .iter()
            .find(|loaded| loaded.source().display_path().ends_with(name))
            .unwrap()
            .id()
    };
    let producer = summaries
        .iter()
        .position(|summary| summary.module == module("producer.ash"))
        .unwrap();
    let facade = summaries
        .iter()
        .position(|summary| summary.module == module("facade.ash"))
        .unwrap();
    let original_publication = Arc::clone(
        summaries[producer].terms["run"]
            .publication
            .as_ref()
            .unwrap(),
    );
    assert!(Arc::ptr_eq(
        &original_publication,
        summaries[facade].terms["closed"]
            .publication
            .as_ref()
            .unwrap()
    ));
    let child = Arc::clone(
        summaries[producer]
            .source_resource_facts
            .values()
            .find(|fact| fact.spelling == "Child")
            .unwrap(),
    );
    let parent = Arc::clone(
        summaries[producer]
            .source_resource_facts
            .values()
            .find(|fact| fact.spelling == "Parent")
            .unwrap(),
    );
    assert_eq!(child.parameters.len(), 5);
    assert_eq!(child.owned_position, 3);
    assert_eq!(child.host.as_ref().unwrap().position, 1);
    assert_eq!(child.parameters[0].kind, Kind::EffectRow);
    assert_eq!(child.parameters[4].kind, Kind::EffectRow);
    assert!(Arc::ptr_eq(
        &child,
        &summaries[facade].source_resource_facts[&child.id]
    ));
    assert!(Arc::ptr_eq(
        &parent,
        &summaries[facade].source_resource_facts[&parent.id]
    ));
    let owner = summaries[producer]
        .source_owners
        .values()
        .find_map(|fact| match fact {
            crate::foreign::source_access::CheckedForeignNominal::Owner(owner)
                if !owner.owner().retained_parameters().is_empty() =>
            {
                Some(Arc::clone(owner))
            }
            _ => None,
        })
        .unwrap();
    assert_eq!(owner.owner().retained_parameters(), &[2]);
    assert_eq!(owner.owned_parameter(), 3);
    let crate::foreign::source_access::CheckedForeignNominal::Owner(forwarded) =
        &summaries[facade].source_owners[&owner.nominal()]
    else {
        panic!("facade must retain the exact original checked Owner category");
    };
    assert!(Arc::ptr_eq(&owner, forwarded));
    assert!(
        !summaries[facade]
            .source_resource_types
            .contains_key("Child")
    );
    assert!(
        !summaries[facade]
            .source_resource_types
            .contains_key("Parent")
    );
    assert!(!summaries[facade].nominals.contains_key("ChildState"));
    assert!(!summaries[facade].terms.contains_key("run"));

    // These operations receive only completed summaries; dependency bodies are
    // not checked again. Resident source remains declaration provenance only.
    crate::elaborate::check_module(resolve_consumer(&graph, &summaries).unwrap())
        .expect("intact renamed body-free facade must admit its consumer");
    let native_count = summaries[facade].native_symbols.len();
    assert!(native_count > 0);
    let removed = summaries[facade]
        .source_resource_facts
        .remove(&child.id)
        .unwrap();
    assert!(Arc::ptr_eq(&removed, &child));
    assert!(Arc::ptr_eq(
        &original_publication,
        summaries[facade].terms["closed"]
            .publication
            .as_ref()
            .unwrap()
    ));
    assert_eq!(summaries[facade].native_symbols.len(), native_count);
    assert!(Arc::ptr_eq(
        &child,
        &summaries[producer].source_resource_facts[&child.id]
    ));
    let error = match resolve_consumer(&graph, &summaries) {
        Err(ResolveModuleError::Resolution(error)) => error,
        other => panic!("expected semantic facade summary refusal, got {other:?}"),
    };
    assert_eq!(error.reason, ResolveReason::InternalState);
    let entry = graph
        .modules()
        .iter()
        .find(|loaded| loaded.id() == graph.entry())
        .unwrap();
    let facade_import = entry
        .dependencies()
        .iter()
        .find(|edge| edge.target() == summaries[facade].module)
        .unwrap();
    let selected_span = entry
        .surface()
        .imports
        .iter()
        .filter(|import| import.span == facade_import.import_span())
        .find_map(|import| match &import.selection {
            crate::surface::SurfaceImportSelection::Targeted(items) => {
                items.iter().find_map(|item| match item {
                    crate::surface::SurfaceImportItem::Name { name, span, .. }
                        if name.text == "closed" =>
                    {
                        Some(*span)
                    }
                    _ => None,
                })
            }
            crate::surface::SurfaceImportSelection::Qualified { .. } => None,
        })
        .unwrap();
    assert_eq!(error.primary.span(), selected_span);
    // The missing Child is reached while retaining imported ResourceApply
    // metadata, after initial summary authentication. This existing label
    // distinguishes that route; it does not add a diagnostic context contract.
    assert_eq!(
        error.primary.message(),
        "an exported type references missing resource metadata"
    );
    assert!(
        summaries[facade]
            .source_resource_facts
            .insert(child.id, removed)
            .is_none()
    );
    crate::elaborate::check_module(resolve_consumer(&graph, &summaries).unwrap())
        .expect("fresh intact retry after local erasure must still admit");
}
