//! Capture-only declaration closure controls; no checked native execution.

use super::checked_wrapper_tests::wrapper_summary_from_source;
use super::*;

const GLOBAL_SOURCE: &str =
    include_str!("../../tests/fixtures/checked-declaration-closure/global.ash");

fn summary() -> ExportSummary {
    wrapper_summary_from_source(GLOBAL_SOURCE)
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
    for ty in summary.terms["select"].capture.types(&mut work).unwrap() {
        collect_nominal_identities(ty, &mut identities, &mut work).unwrap();
    }
    identities
}

fn assert_capture_only_held(summary: &ExportSummary) -> NominalTypeId {
    authenticate_default(summary).unwrap();
    assert_eq!(summary.terms.len(), 1);
    assert!(summary.terms.contains_key("select"));
    // Held is the first module nominal; establish the real graph edge before
    // any metadata lookup, so a missing hidden row cannot hide a weak fixture.
    let held_id = NominalTypeId::new(summary.module, 0);
    assert!(captured_nominals(summary).contains(&held_id));
    let held = summary
        .hidden_nominals
        .get(&held_id)
        .expect("captured Held kind metadata");
    assert_eq!(held.spelling, "Held");
    assert!(held.display_is_private);
    assert_eq!(held.id.module(), summary.module);
    assert_eq!(held.constructor_count, 1);
    assert_eq!(held.access, ImportedTypeAccess::Hidden);
    assert!(held.constructors.is_empty());
    assert!(summary.hidden_nominal_order.contains(&held.id));
    assert!(
        !summary
            .hidden_constructors
            .keys()
            .any(|id| id.owner() == held.id)
    );
    assert!(!summary.nominal_names_by_id.contains_key(&held.id));
    assert!(!summary.nominals.values().any(|fact| fact.id == held.id));
    assert!(
        !summary
            .constructors
            .values()
            .any(|fact| fact.id.owner() == held.id)
    );
    assert!(
        !summary
            .constructor_names_by_id
            .keys()
            .any(|id| id.owner() == held.id)
    );
    assert!(!summary.canonical_representations.contains_key(&held.id));
    assert!(
        captured_nominals(summary).contains(&held.id),
        "the real published capture must retain Held until the returned closure destructures it"
    );
    let mut outward = HashSet::new();
    collect_nominal_identities(
        &summary.terms["select"].scheme.value_type,
        &mut outward,
        &mut TypeWorkBudget::default(),
    )
    .unwrap();
    assert!(
        !outward.contains(&held.id),
        "outward scheme must not rescue Held"
    );
    assert!(summary.terms["select"].scheme.requirements.is_empty());
    assert!(summary.implementations.is_empty());
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
    held.id
}

fn erase_hidden_nominal(summary: &mut ExportSummary, id: NominalTypeId) {
    assert!(summary.hidden_nominals.remove(&id).is_some());
    summary
        .hidden_nominal_order
        .retain(|retained| *retained != id);
    summary
        .hidden_constructors
        .retain(|constructor, _| constructor.owner() != id);
    summary
        .hidden_constructor_order
        .retain(|constructor| constructor.owner() != id);
}

#[test]
fn checked_declaration_closure_global_capture_only_control() {
    let summary = summary();
    assert_capture_only_held(&summary);
}

#[test]
fn checked_declaration_closure_global_rejects_required_hidden_metadata_erasure() {
    let mut summary = summary();
    let held = assert_capture_only_held(&summary);
    let global = &summary.terms["select"];
    let publication = Arc::clone(global.publication.as_ref().unwrap());
    let capture = global.capture.clone();
    let native = summary
        .native_symbols
        .iter()
        .map(|(id, symbol)| (*id, Arc::clone(symbol)))
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
    erase_hidden_nominal(&mut summary, held);
    let retained = &summary.terms["select"];
    assert!(Arc::ptr_eq(
        &publication,
        retained.publication.as_ref().unwrap()
    ));
    assert_eq!(retained.capture, capture);
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
    assert!(!summary.hidden_nominal_order.contains(&held));
    assert!(
        !summary
            .hidden_constructors
            .keys()
            .any(|id| id.owner() == held)
    );
    assert!(
        !summary
            .hidden_constructor_order
            .iter()
            .any(|id| id.owner() == held)
    );
    assert_eq!(
        authenticate_default(&summary),
        Err(ResolvedBuildFailure::InvalidState),
        "a completed global publication/capture cannot replace required hidden nominal/constructor metadata"
    );
}

#[test]
fn checked_declaration_closure_unreferenced_private_spare_is_not_required() {
    let mut summary = summary();
    let held = assert_capture_only_held(&summary);
    let spare = summary
        .hidden_nominals
        .values()
        .find(|fact| fact.spelling == "Spare")
        .map(|fact| fact.id);
    if let Some(spare) = spare {
        assert!(!captured_nominals(&summary).contains(&spare));
        let mut outward = HashSet::new();
        collect_nominal_identities(
            &summary.terms["select"].scheme.value_type,
            &mut outward,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        assert!(!outward.contains(&spare));
        erase_hidden_nominal(&mut summary, spare);
        authenticate_default(&summary).unwrap();
    }
    assert!(!summary.nominals.contains_key("Spare"));
    assert!(
        !summary
            .hidden_nominals
            .values()
            .any(|fact| fact.spelling == "Spare")
    );
    assert!(summary.hidden_nominals.contains_key(&held));
}
