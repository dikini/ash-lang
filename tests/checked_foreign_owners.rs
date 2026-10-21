//! Passive static checked-owner binding; no lifecycle call or native execution.

use ash::{
    foreign::source_contract::{
        ForeignContractReason, prepare_checked_foreign_library, prepare_foreign_library,
    },
    module::{ModuleGraph, ModuleRoots},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason},
    resolved::CheckedModule,
    types::Kind,
};

fn graph() -> ModuleGraph {
    ash::module::load_module_graph(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/checked-owner-binding/owner.ash"),
        &ModuleRoots::empty(),
    )
    .expect("the passive checked-owner fixture must load and parse")
}

fn check_graph(
    graph: &ModuleGraph,
    checked_profile: bool,
) -> Result<Vec<CheckedModule>, ResolveModuleError> {
    let mut checked: Vec<CheckedModule> = Vec::new();
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
        checked.push(ash::elaborate::check_module(resolved)
            .expect("resolved passive owner declarations must complete source checking without lifecycle execution"));
    }
    Ok(checked)
}

#[test]
fn checked_foreign_owner_preparation_retains_distinct_host_owned_slots_and_assumptions() {
    let graph = graph();
    let loaded = graph.module(graph.entry()).unwrap();
    assert_eq!(loaded.surface().foreign_libraries.len(), 1);
    let prepared =
        prepare_checked_foreign_library(loaded.id(), &loaded.surface().foreign_libraries[0])
            .expect("the original passive checked owner contract must prepare before binding");
    assert_eq!(prepared.owners().len(), 1);
    let owner = &prepared.owners()[0];
    assert_eq!(owner.name(), "State");
    assert_eq!(
        owner
            .parameters()
            .iter()
            .map(|parameter| parameter.name())
            .collect::<Vec<_>>(),
        ["H", "R"]
    );
    assert!(
        owner
            .parameters()
            .iter()
            .all(|parameter| parameter.kind() == &Kind::Type)
    );
    assert_eq!(owner.owned_parameter(), 1);
    assert!(owner.retained_parameters().is_empty());
    let contract = prepared.checked_contract().unwrap();
    assert_eq!(contract.owners().len(), 1);
    assert_eq!(contract.owners()[0].member_index(), owner.member_index());
    assert_eq!(contract.owners()[0].host_parameter(), 0);
    assert_ne!(
        contract.owners()[0].host_parameter(),
        owner.owned_parameter()
    );
    assert_eq!(contract.assumptions().len(), 1);
    let assumption = &contract.assumptions()[0];
    assert_eq!(assumption.name(), "Callee");
    assert_eq!(
        assumption.description(),
        "the admitted native owner contract holds"
    );
    assert_eq!(prepared.symbols().len(), 2);
    assert_eq!(contract.symbols().len(), 2);
    for (symbol, selected) in prepared.symbols().iter().zip(contract.symbols()) {
        assert_eq!(
            symbol
                .parameters()
                .iter()
                .map(|parameter| parameter.name())
                .collect::<Vec<_>>(),
            ["H", "R"]
        );
        assert!(
            symbol
                .parameters()
                .iter()
                .all(|parameter| parameter.kind() == &Kind::Type)
        );
        assert_eq!(selected.member_index(), symbol.member_index());
        assert_eq!(selected.host_parameter(), 0);
        assert_eq!(selected.assumption_members(), &[assumption.member_index()]);
        assert!(!selected.minimum_assumptions().is_empty());
    }
    assert_eq!(prepared.symbols()[0].name(), "Allocate");
    assert_eq!(prepared.symbols()[1].name(), "Free");
    assert_eq!(
        owner.teardown_member(),
        prepared.symbols()[1].member_index()
    );
}

#[test]
fn checked_foreign_passive_owner_declarations_resolve_and_check_explicitly() {
    let graph = graph();
    let checked = check_graph(&graph, true)
        .expect("the explicit static profile must bind passive checked owner declarations");
    assert_eq!(checked.len(), graph.modules().len());
    let owner = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .unwrap();
    let state = owner
        .registry()
        .nominals()
        .iter()
        .find(|nominal| nominal.spelling == "State")
        .expect("the original opaque owner nominal remains bound");
    assert!(state.constructors.is_empty());
    let parameters = owner.registry().nominal_parameters(state.id).unwrap();
    assert_eq!(parameters.len(), 2);
    assert_eq!(parameters[0].spelling, "H");
    assert_eq!(parameters[1].spelling, "R");
    assert_ne!(parameters[0].id, parameters[1].id);
    assert!(
        parameters
            .iter()
            .all(|parameter| parameter.kind == Kind::Type)
    );
    for name in ["Allocate", "Free"] {
        let effect = owner
            .registry()
            .effects()
            .iter()
            .find(|effect| effect.spelling == name)
            .expect("original checked owner operation remains bound");
        assert!(effect.native_contract.is_some());
        assert_eq!(effect.parameters.len(), 2);
        assert_eq!(effect.parameters[0].spelling, "H");
        assert_eq!(effect.parameters[1].spelling, "R");
        assert_ne!(effect.parameters[0].id, effect.parameters[1].id);
    }
    // This private declaration fixture exports only idle; its source-check
    // success does not establish body-free owner import or lifecycle support.
    assert_eq!(owner.definitions().len(), 1);
}

#[test]
fn checked_foreign_passive_owner_is_refused_by_default_resolution() {
    let graph = graph();
    match check_graph(&graph, false) {
        Err(ResolveModuleError::Resolution(error)) => {
            assert_eq!(error.reason, ResolveReason::ForeignContract)
        }
        other => panic!("default resolution must refuse checked owner intent: {other:?}"),
    }
}

#[test]
fn checked_foreign_passive_owner_is_refused_by_legacy_abi_preparation() {
    let graph = graph();
    let loaded = graph.module(graph.entry()).unwrap();
    let error = prepare_foreign_library(loaded.id(), &loaded.surface().foreign_libraries[0])
        .expect_err("checked declarations must never enter legacy ABI preparation");
    assert_eq!(error.reason(), ForeignContractReason::UnimplementedContract);
    assert_eq!(error.span().range().end() - error.span().range().start(), 7);
}
