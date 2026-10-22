//! Static scalar checked Borrow preparation/binding; no native execution.

use ash::{
    foreign::source_contract::{
        CheckedNativeAssumption, PreparedAbiResult, PreparedOperandSource, PreparedOwnerArgument,
        PreparedOwnerCall, prepare_checked_foreign_library,
    },
    module::{ModuleGraph, ModuleRoots},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason},
    resolved::{CheckedModule, ResolvedModule},
    types::Kind,
};

fn graph() -> ModuleGraph {
    ash::module::load_module_graph(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/checked-scalar-borrow/owner.ash"),
        &ModuleRoots::empty(),
    )
    .expect("the genuine scalar Borrow fixture must load and parse")
}

fn assert_prepared_borrow(graph: &ModuleGraph) {
    let loaded = graph.module(graph.entry()).unwrap();
    assert_eq!(loaded.surface().foreign_libraries.len(), 1);
    let prepared =
        prepare_checked_foreign_library(loaded.id(), &loaded.surface().foreign_libraries[0])
            .expect("the genuine checked scalar Current contract must prepare before binding");
    assert_eq!(prepared.owners().len(), 1);
    let owner = &prepared.owners()[0];
    assert_eq!(owner.name(), "State");
    assert_eq!(owner.owned_parameter(), 1);
    assert!(owner.retained_parameters().is_empty());
    assert_eq!(prepared.symbols().len(), 3);
    let (index, read) = prepared
        .symbols()
        .iter()
        .enumerate()
        .find(|(_, symbol)| symbol.name() == "Read")
        .unwrap();
    assert_eq!(
        index, 2,
        "existing acquisition/teardown order remains intact"
    );
    assert_eq!(read.native_name(), "ash_owner_read");
    assert_eq!(
        read.parameters()
            .iter()
            .map(|parameter| parameter.name())
            .collect::<Vec<_>>(),
        ["H", "R"]
    );
    assert!(
        read.parameters()
            .iter()
            .all(|formal| formal.kind() == &Kind::Type)
    );
    let Some(PreparedOwnerCall::Borrow {
        application,
        current_operand,
        ..
    }) = read.owner_call()
    else {
        panic!("Read must prepare as an actual nonconsuming owner Borrow");
    };
    assert_eq!(application.owner(), 0);
    assert_eq!(*current_operand, 0);
    assert!(matches!(
        application.arguments(),
        [
            PreparedOwnerArgument::Type(0),
            PreparedOwnerArgument::Type(1)
        ]
    ));
    assert_eq!(read.operands().len(), 1);
    assert!(
        matches!(read.operands()[0].source(), PreparedOperandSource::Current(path) if path == &[0])
    );
    assert!(matches!(read.result(), PreparedAbiResult::Scalar(_)));
    assert!(read.access_result().is_none());
    assert!(read.destruction_operands().is_empty());
    let contract = prepared.checked_contract().unwrap();
    assert_eq!(contract.owners()[0].member_index(), owner.member_index());
    assert_eq!(contract.owners()[0].host_parameter(), 0);
    let selected = &contract.symbols()[index];
    assert_eq!(selected.member_index(), read.member_index());
    assert_eq!(selected.host_parameter(), 0);
    assert_ne!(selected.host_parameter(), owner.owned_parameter());
    let callee = contract
        .assumptions()
        .iter()
        .find(|assumption| assumption.name() == "Callee")
        .unwrap();
    assert_eq!(
        callee.description(),
        "the admitted native owner contract holds"
    );
    assert_eq!(selected.assumption_members(), &[callee.member_index()]);
    for premise in [
        CheckedNativeAssumption::NativeOwnerLifetimeAndDisposition,
        CheckedNativeAssumption::SerializedNativeAccess,
        CheckedNativeAssumption::NativeAliasingAndNonInterference,
    ] {
        assert!(selected.minimum_assumptions().contains(&premise));
    }
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
            ash::resolve::resolve_checked_foreign_module(loaded, &dependencies)
        } else {
            ash::resolve::resolve_module(loaded, &dependencies)
        }?;
        if loaded.id() == graph.entry() {
            return Ok(resolved);
        }
        checked.push(
            ash::elaborate::check_module(resolved)
                .expect("actual builtin dependency checks before scalar Borrow binding"),
        );
    }
    unreachable!("loaded graph contains its entry")
}

#[test]
fn checked_foreign_scalar_borrow_prepares_current_scalar_and_original_host() {
    assert_prepared_borrow(&graph());
}

#[test]
fn checked_foreign_scalar_borrow_binds_through_explicit_static_profile() {
    let graph = graph();
    assert_prepared_borrow(&graph);
    let resolved = resolve_entry(&graph, true)
        .expect("prepared scalar checked Borrow must bind before direct-handler source checking");
    assert_eq!(resolved.module(), graph.entry());
}

#[test]
fn checked_foreign_scalar_borrow_default_profile_still_refuses() {
    let graph = graph();
    assert_prepared_borrow(&graph);
    match resolve_entry(&graph, false) {
        Err(ResolveModuleError::Resolution(error)) => {
            assert_eq!(error.reason, ResolveReason::ForeignContract);
        }
        other => panic!("default resolution cannot admit checked Borrow: {other:?}"),
    }
}
