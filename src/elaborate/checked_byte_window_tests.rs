//! Genuine checked initialized-owner and view prerequisites; no native execution.

use super::*;
use crate::{
    foreign::source_contract::{
        CheckedNativeAssumption, PreparedAccessResult, PreparedAddressRepresentation,
        PreparedForeignExtent, PreparedOwnerArgument, PreparedOwnerCall,
        prepare_checked_foreign_library,
    },
    resolve::{DependencyExports, ResolveModuleError, ResolveReason},
    resolved::ResolvedModule,
};

const SOURCE: &str = include_str!("../../tests/fixtures/checked-byte-windows/owner.ash");

fn fixture() -> ModuleGraph {
    graph_with_entry(SOURCE, None)
}

fn assert_prepared(graph: &ModuleGraph) {
    let loaded = graph.module(graph.entry()).unwrap();
    let prepared =
        prepare_checked_foreign_library(loaded.id(), &loaded.surface().foreign_libraries[0])
            .expect("genuine checked initialized State/view contracts prepare before binding");
    assert_eq!(prepared.owners().len(), 1);
    let owner = &prepared.owners()[0];
    assert_eq!(owner.name(), "State");
    assert_eq!(owner.representation(), PreparedAddressRepresentation::Bytes);
    assert_eq!(owner.owned_parameter(), 1);
    assert!(owner.retained_parameters().is_empty());
    let contract = prepared.checked_contract().unwrap();
    assert_eq!(contract.owners()[0].host_parameter(), 0);
    let allocate = &prepared.symbols()[0];
    let Some(PreparedOwnerCall::Acquire {
        application,
        initialized_bytes: Some(initialized),
        ..
    }) = allocate.owner_call()
    else {
        panic!("actual acquisition must retain initialized-byte evidence");
    };
    assert_eq!(application.owner(), 0);
    assert_eq!(
        application.arguments(),
        &[
            PreparedOwnerArgument::Type(0),
            PreparedOwnerArgument::Type(1)
        ]
    );
    assert_eq!(initialized.extent(), &[1]);
    assert_eq!(prepared.accesses().len(), 2);
    for (family, name, extent, preserving) in [
        (
            0,
            "ByteView",
            PreparedForeignExtent::Bytes,
            vec!["QueryBytes", "ByteLength"],
        ),
        (1, "NulView", PreparedForeignExtent::Nul, vec!["QueryNul"]),
    ] {
        let access = &prepared.accesses()[family];
        assert_eq!(access.name(), name);
        assert_eq!(access.window_parameter(), 0);
        assert_eq!(access.extent(), extent);
        assert_eq!(
            access
                .parameters()
                .iter()
                .map(|p| p.name())
                .collect::<Vec<_>>(),
            ["W", "H", "R"]
        );
        assert_eq!(access.owner().owner(), 0);
        assert_eq!(
            access.owner().arguments(),
            &[
                PreparedOwnerArgument::Type(1),
                PreparedOwnerArgument::Type(2)
            ]
        );
        assert_eq!(
            access
                .preserving_members()
                .iter()
                .map(|(member, _)| prepared
                    .symbols()
                    .iter()
                    .find(|s| s.member_index() == *member)
                    .unwrap()
                    .name())
                .collect::<Vec<_>>(),
            preserving
        );
    }
    let callee = contract
        .assumptions()
        .iter()
        .find(|a| a.name() == "Callee")
        .unwrap();
    for (index, symbol) in prepared.symbols().iter().enumerate() {
        let selected = &contract.symbols()[index];
        assert_eq!(selected.member_index(), symbol.member_index());
        assert_eq!(selected.host_parameter(), if index < 2 { 0 } else { 1 });
        assert_eq!(selected.assumption_members(), &[callee.member_index()]);
        assert!(
            selected
                .minimum_assumptions()
                .contains(&CheckedNativeAssumption::NativeOwnerLifetimeAndDisposition)
        );
        if index >= 2 {
            assert_eq!(
                symbol
                    .parameters()
                    .iter()
                    .map(|p| p.name())
                    .collect::<Vec<_>>(),
                ["W", "H", "R"]
            );
        }
    }
    for (name, family) in [("QueryBytes", 0), ("QueryNul", 1)] {
        let symbol = prepared
            .symbols()
            .iter()
            .find(|s| s.name() == name)
            .unwrap();
        let Some(PreparedAccessResult::View {
            application, keys, ..
        }) = symbol.access_result()
        else {
            panic!("actual view result");
        };
        assert_eq!(application.family(), family);
        assert_eq!(
            application.arguments(),
            &[
                PreparedOwnerArgument::Type(0),
                PreparedOwnerArgument::Type(1),
                PreparedOwnerArgument::Type(2)
            ]
        );
        assert_eq!(keys, &[vec![1]]);
    }
    let length = prepared
        .symbols()
        .iter()
        .find(|s| s.name() == "ByteLength")
        .unwrap();
    let Some(PreparedAccessResult::Extent {
        application,
        view,
        keys,
        ..
    }) = length.access_result()
    else {
        panic!("actual extent result");
    };
    assert_eq!(application.family(), 0);
    assert_eq!(
        application.arguments(),
        &[
            PreparedOwnerArgument::Type(0),
            PreparedOwnerArgument::Type(1),
            PreparedOwnerArgument::Type(2)
        ]
    );
    assert_eq!(view, &[2]);
    assert_eq!(keys, &[vec![1]]);
}

// Check genuine dependency modules, then return the root at the precise resolved
// binding boundary. Connected source/summary/Core checks are a separate test set.
fn resolve_entry(
    graph: &ModuleGraph,
    checked_profile: bool,
) -> Result<ResolvedModule, ResolveModuleError> {
    let mut checked = Vec::<CheckedModule>::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(
                    edge,
                    checked
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = if checked_profile {
            crate::resolve::resolve_checked_foreign_module(loaded, &dependencies)
        } else {
            crate::resolve::resolve_module(loaded, &dependencies)
        }?;
        if loaded.id() == graph.entry() {
            return Ok(resolved);
        }
        checked.push(
            crate::elaborate::check_module(resolved)
                .expect("actual builtin dependency checks before byte/window binding"),
        );
    }
    unreachable!("loaded graph contains its entry")
}

#[test]
fn checked_byte_window_prepares_initialized_state_and_actual_view_extent_contracts() {
    assert_prepared(&fixture());
}

#[test]
fn checked_byte_window_checked_primitive_inventory_resolves() {
    let graph = fixture();
    assert_prepared(&graph);
    resolve_entry(&graph, true)
        .expect("prepared initialized State and real view/extent contracts must bind before checked primitive source admission");
}

#[test]
fn checked_byte_window_default_profile_refuses() {
    let graph = fixture();
    assert_prepared(&graph);
    match resolve_entry(&graph, false) {
        Err(ResolveModuleError::Resolution(error)) => {
            assert_eq!(error.reason, ResolveReason::ForeignContract)
        }
        other => panic!("default profile must refuse checked initialized State: {other:?}"),
    }
}

// Resolve names using existing builtin spellings ONLY to reach checked owner
// binding. This root is never source-checked: legacy byte/copy functions grant
// no checked State/view permission and cannot stand in for the new identities.
#[test]
fn checked_byte_window_initialized_owner_binding_after_name_isolation() {
    let source = SOURCE
        .replace("Foreign.checked_byte_read", "Foreign.byte_read")
        .replace("Foreign.checked_byte_write", "Foreign.byte_write")
        .replace("Foreign.checked_copy_bytes", "Foreign.copy_bytes")
        .replace("Foreign.checked_copy_nul", "Foreign.copy_nul");
    let graph = graph_with_entry(&source, None);
    assert_prepared(&graph);
    resolve_entry(&graph, true)
        .expect("genuine prepared checked initialized owner/view contracts must bind independently of missing new builtin names");
}

#[test]
fn checked_byte_window_all_four_primitives_check_actual_source_and_summary() {
    let graph = fixture();
    assert_prepared(&graph);
    let checked = check_graph(&graph)
        .expect("all four checked primitives need genuine initialized State and actual lexical view/extent window source admission");
    let producer = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .unwrap();
    assert!(producer.source_resource_code().is_some());
    let registry = producer.registry();
    for name in ["Allocate", "Free", "QueryBytes", "ByteLength", "QueryNul"] {
        let effect = registry
            .effects()
            .iter()
            .find(|effect| effect.spelling == name)
            .unwrap();
        let original = registry
            .native_symbol(crate::types::OperationId::new(effect.id, 0))
            .unwrap();
        assert!(original.prepared().checked_contract().is_some());
        assert!(original.owner().is_some());
    }
}
