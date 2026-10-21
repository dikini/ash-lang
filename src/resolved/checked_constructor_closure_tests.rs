//! Constructor-payload declaration closure, distinct from capture-root checks.

use super::checked_wrapper_tests::wrapper_summary_from_source;
use super::*;

const PRODUCER: &str =
    include_str!("../../tests/fixtures/checked-constructor-closure/producer.ash");

fn summary() -> ExportSummary {
    wrapper_summary_from_source(PRODUCER)
}

fn authenticate_default(summary: &ExportSummary) -> Result<(), ResolvedBuildFailure> {
    summary.authenticate(
        &mut TypeWorkBudget::default(),
        &mut crate::interface::InterfaceConstraintBudget::default(),
    )
}

fn assert_payload_only_leaf(summary: &ExportSummary) -> (NominalTypeId, NominalTypeId) {
    authenticate_default(summary).unwrap();
    let leaf = NominalTypeId::new(summary.module, 0);
    let donor = NominalTypeId::new(summary.module, 1);
    assert_ne!(leaf, donor);
    for (id, spelling) in [(leaf, "Leaf"), (donor, "Donor")] {
        let hidden = summary
            .hidden_nominals
            .get(&id)
            .expect("payload dependency kind metadata");
        assert_eq!(hidden.spelling, spelling);
        assert!(hidden.display_is_private);
        assert_eq!(hidden.access, ImportedTypeAccess::Hidden);
        assert_eq!(hidden.constructor_count, 1);
        assert_eq!(hidden.parameter_count, 0);
        assert!(hidden.parameters.is_empty());
        assert!(hidden.constructors.is_empty());
        assert!(summary.hidden_nominal_order.contains(&id));
        assert!(!summary.nominal_names_by_id.contains_key(&id));
        assert!(!summary.nominals.values().any(|fact| fact.id == id));
        assert!(
            !summary
                .constructors
                .values()
                .any(|fact| fact.id.owner() == id)
        );
        assert!(
            !summary
                .hidden_constructors
                .keys()
                .any(|constructor| constructor.owner() == id)
        );
        assert!(!summary.canonical_representations.contains_key(&id));
    }
    for (name, payload) in [("Envelope", leaf), ("Witness", donor)] {
        let nominal = &summary.nominals[name];
        assert_eq!(nominal.access, ExportedTypeAccess::Transparent);
        assert_eq!(nominal.constructors.len(), 1);
        let constructor = &summary.constructors[name];
        assert_eq!(constructor.id.owner(), nominal.id);
        assert_eq!(nominal.constructors[0], constructor.id);
        assert_eq!(constructor.payload.as_ref(), Some(&Type::Nominal(payload)));
        assert!(constructor.scheme.type_parameters.is_empty());
        assert!(constructor.scheme.requirements.is_empty());
        assert!(matches!(&constructor.scheme.value_type,
            Type::Function(domain, result)
            if domain.as_ref() == &Type::Nominal(payload)
                && result.as_ref() == &Type::Nominal(nominal.id)));
        assert!(!summary.hidden_constructors.contains_key(&constructor.id));
    }
    assert_eq!(summary.terms.len(), 2);
    assert!(summary.terms.contains_key("make") && summary.terms.contains_key("inspect"));
    let mut work = TypeWorkBudget::default();
    for global in summary.terms.values() {
        let mut outward = HashSet::new();
        collect_nominal_identities(&global.scheme.value_type, &mut outward, &mut work).unwrap();
        assert!(
            !outward.contains(&leaf),
            "global outward type must not rescue Leaf"
        );
        assert!(global.scheme.requirements.is_empty());
        let mut captured = HashSet::new();
        for ty in global.capture.types(&mut work).unwrap() {
            collect_capture_external_nominals(ty, &mut captured, &mut work).unwrap();
        }
        assert!(
            !captured.contains(&leaf),
            "fixture must reach Leaf through constructor metadata, not capture.types"
        );
    }
    assert!(summary.implementations.is_empty());
    assert_eq!(summary.native_symbols.len(), 1);
    let symbol = summary.native_symbols.values().next().unwrap();
    let contract = symbol.prepared().checked_contract().unwrap();
    assert_eq!(contract.assumptions().len(), 1);
    assert_eq!(contract.assumptions()[0].name(), "Callee");
    assert_eq!(contract.symbols().len(), 1);
    assert_eq!(
        contract.symbols()[0].assumption_members(),
        &[contract.assumptions()[0].member_index()]
    );
    assert!(!contract.symbols()[0].minimum_assumptions().is_empty());
    (leaf, donor)
}

fn assert_mutation_rejected(mutate: impl FnOnce(&mut ExportSummary, NominalTypeId, NominalTypeId)) {
    let mut summary = summary();
    let (leaf, donor) = assert_payload_only_leaf(&summary);
    let globals = summary
        .terms
        .iter()
        .map(|(name, global)| {
            (
                name.clone(),
                Arc::clone(global.publication.as_ref().unwrap()),
                global.capture.clone(),
            )
        })
        .collect::<Vec<_>>();
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
    let envelope_id = summary.constructors["Envelope"].id;
    let envelope_origin = summary.constructors["Envelope"].origin.clone();
    mutate(&mut summary, leaf, donor);
    assert_eq!(summary.constructors["Envelope"].id, envelope_id);
    assert_eq!(summary.constructors["Envelope"].origin, envelope_origin);
    assert_eq!(
        summary.nominals["Envelope"].access,
        ExportedTypeAccess::Transparent
    );
    for (name, publication, capture) in globals {
        let global = &summary.terms[&name];
        assert!(Arc::ptr_eq(
            &publication,
            global.publication.as_ref().unwrap()
        ));
        assert_eq!(global.capture, capture);
        authenticate_global_publication(
            global,
            &mut TypeWorkBudget::default(),
            &mut crate::interface::InterfaceConstraintBudget::default(),
        )
        .unwrap();
    }
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
        "coherent constructor declaration closure mutation requires independent rejection"
    );
}

#[test]
fn checked_constructor_closure_payload_only_control() {
    assert_payload_only_leaf(&summary());
}

#[test]
fn checked_constructor_closure_rejects_missing_payload_leaf() {
    assert_mutation_rejected(|summary, leaf, _| {
        assert!(summary.hidden_nominals.remove(&leaf).is_some());
        summary.hidden_nominal_order.retain(|id| *id != leaf);
        assert_eq!(
            summary.constructors["Envelope"].payload.as_ref(),
            Some(&Type::Nominal(leaf))
        );
    });
}

#[test]
fn checked_constructor_closure_rejects_coherent_payload_donor() {
    assert_mutation_rejected(|summary, leaf, donor| {
        assert!(summary.hidden_nominals.contains_key(&leaf));
        assert!(summary.hidden_nominals.contains_key(&donor));
        let envelope = summary.nominals["Envelope"].id;
        let constructor = summary.constructors.get_mut("Envelope").unwrap();
        constructor.payload = Some(Type::Nominal(donor));
        constructor.scheme.value_type = Type::Function(
            Box::new(Type::Nominal(donor)),
            Box::new(Type::Nominal(envelope)),
        );
        assert_eq!(constructor.payload.as_ref(), Some(&Type::Nominal(donor)));
    });
}

#[test]
fn checked_constructor_closure_unreferenced_spare_is_not_required() {
    let mut summary = summary();
    let (leaf, donor) = assert_payload_only_leaf(&summary);
    let spare = summary
        .hidden_nominals
        .values()
        .find(|fact| fact.spelling == "Spare")
        .map(|fact| fact.id);
    if let Some(spare) = spare {
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
    assert!(!summary.nominals.contains_key("Spare"));
    assert!(
        !summary
            .hidden_nominals
            .values()
            .any(|fact| fact.spelling == "Spare")
    );
    assert!(summary.hidden_nominals.contains_key(&leaf));
    assert!(summary.hidden_nominals.contains_key(&donor));
}
