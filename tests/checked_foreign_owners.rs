//! Passive static checked-owner binding; no lifecycle call or native execution.

use ash::{
    foreign::source_contract::{
        CheckedNativeAssumption, ForeignContractReason, prepare_checked_foreign_library,
        prepare_foreign_library,
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
        assert!(
            selected
                .minimum_assumptions()
                .contains(&CheckedNativeAssumption::NativeOwnerLifetimeAndDisposition)
        );
        if symbol.name() == "Free" {
            assert!(
                selected
                    .minimum_assumptions()
                    .contains(&CheckedNativeAssumption::SerializedNativeAccess)
            );
        }
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

const OWNER_SOURCE: &str = include_str!("fixtures/checked-owner-binding/owner.ash");

fn variant_graph(producer: &str, consumer: Option<&str>) -> ModuleGraph {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-checked-owner-variant-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let entry = if let Some(consumer) = consumer {
        std::fs::write(directory.join("native.ash"), producer).unwrap();
        std::fs::write(directory.join("entry.ash"), consumer).unwrap();
        directory.join("entry.ash")
    } else {
        std::fs::write(directory.join("entry.ash"), producer).unwrap();
        directory.join("entry.ash")
    };
    let graph = ash::module::load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    graph
}

#[test]
fn checked_foreign_public_passive_owner_import_preserves_original_metadata_without_calls() {
    let producer = OWNER_SOURCE.replace("foreign checked library", "pub foreign checked library");
    let graph = variant_graph(
        &producer,
        Some(
            "import native (State, Allocate, Free, idle)\nmain : Unit -> Int\nmain () = idle ()\n",
        ),
    );
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
        let resolved = ash::resolve::resolve_checked_foreign_module(loaded, &dependencies).unwrap();
        if loaded.id() == graph.entry() {
            let producer = checked
                .iter()
                .find(|module| {
                    module
                        .registry()
                        .nominals()
                        .iter()
                        .any(|nominal| nominal.spelling == "State")
                })
                .unwrap();
            let state = producer
                .registry()
                .nominals()
                .iter()
                .find(|nominal| nominal.spelling == "State")
                .unwrap();
            let imported = resolved
                .imported_facts()
                .nominal(state.id)
                .expect("explicit State import must retain the actual owner nominal");
            assert_eq!(imported.id, state.id);
            assert!(imported.constructors.is_empty());
            assert_eq!(
                imported.parameters.as_ref(),
                producer.registry().nominal_parameters(state.id).unwrap()
            );
            for name in ["Allocate", "Free"] {
                let original = producer
                    .registry()
                    .effects()
                    .iter()
                    .find(|effect| effect.spelling == name)
                    .unwrap();
                let imported = resolved
                    .imported_facts()
                    .effect(original.id)
                    .expect("explicit native effect import must retain metadata");
                assert!(std::sync::Arc::ptr_eq(
                    original.native_contract.as_ref().unwrap(),
                    imported.native_contract.as_ref().unwrap()
                ));
                assert_eq!(imported.parameters, original.parameters);
            }
        }
        checked.push(ash::elaborate::check_module(resolved).unwrap());
    }
    assert_eq!(checked.len(), graph.modules().len());
}

#[test]
fn checked_foreign_passive_void_teardown_preserves_consumed_and_retained_outcomes() {
    for outcome in ["consumed 0", "retained 0"] {
        let source = OWNER_SOURCE.replace(
            "outcome otherwise { consumed 0 }",
            &format!("outcome otherwise {{ {outcome} }}"),
        );
        let graph = variant_graph(&source, None);
        check_graph(&graph, true)
            .expect("void teardown disposition is preserved during passive binding");
    }
}

#[test]
fn checked_foreign_owner_preparation_rejects_owned_or_same_kind_wrong_host() {
    let valid = variant_graph(OWNER_SOURCE, None);
    let root = valid.module(valid.entry()).unwrap();
    prepare_checked_foreign_library(root.id(), &root.surface().foreign_libraries[0]).unwrap();
    let owned_host = OWNER_SOURCE.replacen("host H", "host R", 1);
    let free_extra = OWNER_SOURCE.replace("symbol Free<H, R>", "symbol Free<H, R, Other>");
    let start = free_extra.find("symbol Free").unwrap();
    let wrong_host = format!(
        "{}{}",
        &free_extra[..start],
        free_extra[start..].replacen("host H", "host Other", 1)
    );
    for source in [owned_host, wrong_host] {
        let graph = variant_graph(&source, None);
        let loaded = graph.module(graph.entry()).unwrap();
        let error =
            prepare_checked_foreign_library(loaded.id(), &loaded.surface().foreign_libraries[0])
                .expect_err("owned slot or different Type-kind formal cannot replace exact H");
        assert_eq!(
            error.reason(),
            ForeignContractReason::InvalidCheckedContract
        );
    }
}

#[test]
fn checked_foreign_passive_owner_preserves_complete_row_and_type_formals() {
    let source = OWNER_SOURCE
        .replace(
            "owner State<H, R>",
            "owner State<Before : EffectRow, H, R, After : EffectRow>",
        )
        .replace("State<H, R>", "State<{| Before}, H, R, {| After}>")
        .replace(
            "symbol Allocate<H, R>",
            "symbol Allocate<Before : EffectRow, H, R, After : EffectRow>",
        )
        .replace(
            "symbol Free<H, R>",
            "symbol Free<Before : EffectRow, H, R, After : EffectRow>",
        );
    let graph = variant_graph(&source, None);
    let root = graph.module(graph.entry()).unwrap();
    let prepared =
        prepare_checked_foreign_library(root.id(), &root.surface().foreign_libraries[0]).unwrap();
    assert_eq!(prepared.owners()[0].owned_parameter(), 2);
    assert_eq!(
        prepared.checked_contract().unwrap().owners()[0].host_parameter(),
        1
    );
    let checked = check_graph(&graph, true).unwrap();
    let owner = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .unwrap();
    let state = owner
        .registry()
        .nominals()
        .iter()
        .find(|nominal| nominal.spelling == "State")
        .unwrap();
    let parameters = owner.registry().nominal_parameters(state.id).unwrap();
    assert_eq!(
        parameters
            .iter()
            .map(|parameter| &parameter.kind)
            .collect::<Vec<_>>(),
        [&Kind::EffectRow, &Kind::Type, &Kind::Type, &Kind::EffectRow]
    );
    assert_eq!(
        parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        ["Before", "H", "R", "After"]
    );
    for name in ["Allocate", "Free"] {
        let operation = owner
            .registry()
            .effects()
            .iter()
            .find(|effect| effect.spelling == name)
            .unwrap();
        assert_eq!(
            operation
                .parameters
                .iter()
                .map(|parameter| &parameter.kind)
                .collect::<Vec<_>>(),
            [&Kind::EffectRow, &Kind::Type, &Kind::Type, &Kind::EffectRow]
        );
    }
}

#[test]
fn checked_foreign_host_does_not_authorize_direct_owner_acquisition() {
    let source = format!(
        "{OWNER_SOURCE}main : Unit -> Unit\nmain () = foreign host H {{\n    let ignored = perform Allocate<H, Int>.call 8\n    ()\n}}\n"
    );
    let graph = variant_graph(&source, None);
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
        let resolved = ash::resolve::resolve_checked_foreign_module(loaded, &dependencies)
            .expect("passive checked binding and the actual host request must resolve first");
        let result = ash::elaborate::check_module(resolved);
        if loaded.id() == graph.entry() {
            match result {
                Err(ash::elaborate::TypeError::Source(error)) => {
                    println!("direct checked owner request refusal: {error:?}");
                    assert_eq!(error.reason, ash::elaborate::TypeReason::Argument)
                }
                other => panic!("host alone must not grant owner lifecycle permission: {other:?}"),
            }
            return;
        }
        checked.push(result.unwrap());
    }
    panic!("entry missing");
}

#[test]
fn checked_foreign_passive_opaque_dependency_remains_unsupported_after_preparation() {
    let original = include_str!("fixtures/source-owner/dependent_owner.ash");
    let prefix = original.split("pub type Acquire").next().unwrap();
    let mut source = prefix
        .replace("pub foreign library", "pub foreign checked library")
        .replace("    repr ParentBytes = bytes\n", "")
        .replace("ParentBytes", "Address")
        .replace(", initialized_bytes result from 0", "")
        .replace("Foreign.Call<", "Foreign.CheckedCall<")
        .replace("ParentState<P>", "ParentState<H, P>")
        .replace("ChildState<P, R>", "ChildState<H, P, R>")
        .replace("owned P", "owned P\n        host H")
        .replace("owned R", "owned R\n        host H")
        .replace(
            "operand 0 from",
            "host H\n        assumes {}\n        operand 0 from",
        );
    for (name, parameters) in [
        ("ParentAllocate", "P"),
        ("ParentFree", "P"),
        ("ChildAllocate", "P, R"),
        ("ChildFree", "P, R"),
        ("ChildHold", "P, R"),
    ] {
        source = source.replace(
            &format!("symbol {name}<{parameters}>"),
            &format!("symbol {name}<H, {parameters}>"),
        );
    }
    let graph = variant_graph(&source, None);
    let loaded = graph.module(graph.entry()).unwrap();
    let prepared =
        prepare_checked_foreign_library(loaded.id(), &loaded.surface().foreign_libraries[0])
            .expect("opaque parent/child contract must prepare before dependency binding refusal");
    assert_eq!(prepared.owners().len(), 2);
    assert!(prepared.owners()[0].retained_parameters().is_empty());
    assert_eq!(prepared.owners()[1].retained_parameters(), &[1]);
    match check_graph(&graph, true) {
        Err(ResolveModuleError::Resolution(error)) => {
            assert_eq!(error.reason, ResolveReason::ForeignContract)
        }
        other => panic!("opaque dependent checked owner must remain refused: {other:?}"),
    }
}
