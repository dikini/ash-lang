//! Selected-method parity for capture-only nominal declaration closure.

use super::checked_wrapper_tests::wrapper_summary_from_source;
use super::*;

const SELECTED_SOURCE: &str =
    include_str!("../../tests/fixtures/checked-declaration-closure/selected.ash");

fn summary() -> ExportSummary {
    wrapper_summary_from_source(SELECTED_SOURCE)
}

fn authenticate_default(summary: &ExportSummary) -> Result<(), ResolvedBuildFailure> {
    summary.authenticate(
        &mut TypeWorkBudget::default(),
        &mut crate::interface::InterfaceConstraintBudget::default(),
    )
}

fn captured_nominals(summary: &ExportSummary) -> HashSet<NominalTypeId> {
    let mut work = TypeWorkBudget::default();
    let mut identities = HashSet::new();
    for ty in summary.implementations[0].fact.methods[0]
        .capture
        .types(&mut work)
        .unwrap()
    {
        collect_nominal_identities(ty, &mut identities, &mut work).unwrap();
    }
    identities
}

fn assert_selected_capture_only_held(summary: &ExportSummary) -> NominalTypeId {
    authenticate_default(summary).unwrap();
    assert!(
        summary.terms.is_empty(),
        "only selected evidence publishes the callable"
    );
    assert_eq!(summary.implementations.len(), 1);
    let implementation = &summary.implementations[0];
    assert!(implementation.fact.head_parameters.is_empty());
    assert!(implementation.fact.prerequisites.is_empty());
    assert_eq!(
        implementation.fact.arguments(),
        &[crate::types::KindedArgument::TypeArg(Type::Int)]
    );
    assert_eq!(implementation.fact.methods.len(), 1);
    let method = &implementation.fact.methods[0];
    assert!(method.scheme.requirements.is_empty());
    let held = NominalTypeId::new(summary.module, 0);
    assert!(
        captured_nominals(summary).contains(&held),
        "real selected method capture must reach Held before hidden metadata is consulted"
    );
    let hidden = summary
        .hidden_nominals
        .get(&held)
        .expect("captured private Held metadata");
    assert_eq!(hidden.spelling, "Held");
    assert!(hidden.display_is_private);
    assert_eq!(hidden.access, ImportedTypeAccess::Hidden);
    assert_eq!(hidden.constructor_count, 1);
    assert!(hidden.constructors.is_empty());
    assert!(summary.hidden_nominal_order.contains(&held));
    assert!(!summary.nominal_names_by_id.contains_key(&held));
    assert!(!summary.nominals.values().any(|fact| fact.id == held));
    assert!(
        !summary
            .hidden_constructors
            .keys()
            .any(|id| id.owner() == held)
    );
    assert!(
        !summary
            .constructors
            .values()
            .any(|fact| fact.id.owner() == held)
    );
    assert!(
        !summary
            .constructor_names_by_id
            .keys()
            .any(|id| id.owner() == held)
    );
    assert!(!summary.canonical_representations.contains_key(&held));
    let mut outward = HashSet::new();
    collect_nominal_identities(
        &method.scheme.value_type,
        &mut outward,
        &mut TypeWorkBudget::default(),
    )
    .unwrap();
    assert!(
        !outward.contains(&held),
        "method scheme must not rescue Held"
    );
    for interface in &summary.interfaces {
        for method in &interface.methods {
            let mut outward = HashSet::new();
            collect_nominal_identities(
                &method.value_type,
                &mut outward,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            assert!(
                !outward.contains(&held),
                "interface scheme must not rescue Held"
            );
        }
    }
    assert_eq!(summary.native_symbols.len(), 1);
    let symbol = summary.native_symbols.values().next().unwrap();
    let contract = symbol.prepared().checked_contract().unwrap();
    assert_eq!(contract.assumptions().len(), 1);
    let assumption = &contract.assumptions()[0];
    assert_eq!(assumption.name(), "Callee");
    assert_eq!(
        assumption.description(),
        "the admitted native contract holds"
    );
    assert_eq!(contract.symbols().len(), 1);
    assert_eq!(
        contract.symbols()[0].assumption_members(),
        &[assumption.member_index()]
    );
    assert!(!contract.symbols()[0].minimum_assumptions().is_empty());
    assert!(
        summary
            .requires_checked_foreign_profile(&mut TypeWorkBudget::default())
            .unwrap()
    );
    held
}

#[test]
fn checked_selected_declaration_closure_capture_only_control() {
    assert_selected_capture_only_held(&summary());
}

#[test]
fn checked_selected_declaration_closure_rejects_required_hidden_metadata_erasure() {
    let mut summary = summary();
    let held = assert_selected_capture_only_held(&summary);
    let implementation = &summary.implementations[0];
    let publication = Arc::clone(implementation.publication.as_ref().unwrap());
    let capture = implementation.fact.methods[0].capture.clone();
    let method_id = implementation.fact.methods[0].id;
    let binder = implementation.fact.methods[0].binder;
    let native = summary
        .native_symbols
        .iter()
        .map(|(id, fact)| (*id, Arc::clone(fact)))
        .collect::<Vec<_>>();
    let sources = summary
        .defining_sources
        .iter()
        .map(|(module, source)| (*module, Arc::clone(source)))
        .collect::<Vec<_>>();
    let effects = summary
        .effects
        .iter()
        .map(|effect| effect.id)
        .collect::<Vec<_>>();
    assert!(summary.hidden_nominals.remove(&held).is_some());
    summary.hidden_nominal_order.retain(|id| *id != held);
    let retained = &summary.implementations[0];
    assert!(Arc::ptr_eq(
        &publication,
        retained.publication.as_ref().unwrap()
    ));
    assert_eq!(retained.fact.methods[0].capture, capture);
    assert_eq!(retained.fact.methods[0].id, method_id);
    assert_eq!(retained.fact.methods[0].binder, binder);
    authenticate_implementation_publication(
        &retained.fact,
        retained.publication.as_ref(),
        &mut TypeWorkBudget::default(),
        &mut crate::interface::InterfaceConstraintBudget::default(),
    )
    .unwrap();
    assert!(captured_nominals(&summary).contains(&held));
    for (id, original) in native {
        assert!(Arc::ptr_eq(&original, &summary.native_symbols[&id]));
    }
    for (module, original) in sources {
        assert!(
            summary
                .defining_sources
                .iter()
                .any(|(id, source)| *id == module && Arc::ptr_eq(&original, source))
        );
    }
    assert_eq!(
        summary
            .effects
            .iter()
            .map(|effect| effect.id)
            .collect::<Vec<_>>(),
        effects
    );
    assert_eq!(
        authenticate_default(&summary),
        Err(ResolvedBuildFailure::InvalidState),
        "selected completed publication/capture cannot substitute for required hidden nominal metadata"
    );
}

#[test]
fn checked_selected_declaration_closure_unreferenced_spare_is_not_required() {
    let mut summary = summary();
    let held = assert_selected_capture_only_held(&summary);
    let spare = summary
        .hidden_nominals
        .values()
        .find(|fact| fact.spelling == "Spare")
        .map(|fact| fact.id);
    if let Some(spare) = spare {
        assert!(!captured_nominals(&summary).contains(&spare));
        assert_eq!(
            summary.hidden_nominals[&spare].access,
            ImportedTypeAccess::Hidden
        );
        assert!(summary.hidden_nominals[&spare].constructors.is_empty());
        assert!(
            !summary
                .hidden_constructors
                .keys()
                .any(|id| id.owner() == spare)
        );
        summary.hidden_nominals.remove(&spare);
        summary.hidden_nominal_order.retain(|id| *id != spare);
        authenticate_default(&summary).unwrap();
    }
    assert!(
        !summary
            .hidden_nominals
            .values()
            .any(|fact| fact.spelling == "Spare")
    );
    assert!(!summary.nominals.contains_key("Spare"));
    assert!(summary.hidden_nominals.contains_key(&held));
}
