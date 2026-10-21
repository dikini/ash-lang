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

#[derive(Clone, Copy)]
enum ConsumerMutation {
    MissingLeaf,
    CoherentDonor,
}

fn assert_body_free_consumer_rejects(mutation: ConsumerMutation) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-constructor-consumer-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    std::fs::write(directory.join("native.ash"), PRODUCER).unwrap();
    std::fs::write(directory.join("entry.ash"),
        "import @builtin.foreign as Foreign\nimport native as Native\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = Native.inspect (Native.make 7)\n").unwrap();
    let graph = crate::module::load_module_graph(
        &directory.join("entry.ash"),
        &crate::module::ModuleRoots::empty(),
    )
    .unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    let mut summaries: Vec<ExportSummary> = Vec::new();
    for loaded in graph.modules() {
        if loaded.id() == graph.entry() {
            let dependencies = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    crate::resolve::DependencyExports::new(
                        edge,
                        summaries
                            .iter()
                            .find(|summary| summary.module == edge.target())
                            .unwrap(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let canonical =
                crate::resolve::resolve_checked_foreign_module(loaded, &dependencies).unwrap();
            crate::elaborate::check_module(canonical).unwrap();
            let producer = summaries
                .iter_mut()
                .find(|summary| {
                    summary.terms.contains_key("make") && summary.terms.contains_key("inspect")
                })
                .unwrap();
            let (leaf, donor) = assert_payload_only_leaf(producer);
            match mutation {
                ConsumerMutation::MissingLeaf => {
                    assert!(producer.hidden_nominals.remove(&leaf).is_some());
                    producer.hidden_nominal_order.retain(|id| *id != leaf);
                }
                ConsumerMutation::CoherentDonor => {
                    assert!(producer.hidden_nominals.contains_key(&leaf));
                    assert!(producer.hidden_nominals.contains_key(&donor));
                    let envelope = producer.nominals["Envelope"].id;
                    let constructor = producer.constructors.get_mut("Envelope").unwrap();
                    constructor.payload = Some(Type::Nominal(donor));
                    constructor.scheme.value_type = Type::Function(
                        Box::new(Type::Nominal(donor)),
                        Box::new(Type::Nominal(envelope)),
                    );
                }
            }
            for global in producer.terms.values() {
                authenticate_global_publication(
                    global,
                    &mut TypeWorkBudget::default(),
                    &mut crate::interface::InterfaceConstraintBudget::default(),
                )
                .unwrap();
            }
        }
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                crate::resolve::DependencyExports::new(
                    edge,
                    summaries
                        .iter()
                        .find(|summary| summary.module == edge.target())
                        .unwrap(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = crate::resolve::resolve_checked_foreign_module(loaded, &dependencies);
        if loaded.id() == graph.entry() {
            let error = match resolved {
                Err(crate::resolve::ResolveModuleError::Resolution(error)) => error,
                Ok(resolved) => {
                    crate::elaborate::check_module(resolved)
                        .expect("the mutated summary also passed body-free checking");
                    panic!(
                        "coherent constructor mutation passed body-free resolution and checking"
                    );
                }
                Err(other) => panic!("unexpected dependency refusal: {other:?}"),
            };
            assert_eq!(error.reason, crate::resolve::ResolveReason::InternalState);
            assert_eq!(
                error.subject_fact(),
                Some((
                    "cause",
                    "resolver-internal-cause",
                    "dependency-summary-invalid"
                ))
            );
            return;
        }
        summaries.push(
            crate::elaborate::check_module(resolved.unwrap())
                .unwrap()
                .into_exports(),
        );
    }
    panic!("consumer missing");
}

#[test]
fn checked_constructor_closure_body_free_consumer_rejects_missing_leaf() {
    assert_body_free_consumer_rejects(ConsumerMutation::MissingLeaf);
}

#[test]
fn checked_constructor_closure_body_free_consumer_rejects_coherent_donor() {
    assert_body_free_consumer_rejects(ConsumerMutation::CoherentDonor);
}

impl ResolvedRegistry {
    /// Changes one canonical payload only; Core retains its independent body
    /// annotations. There is no constructor scheme mirror in this registry.
    pub(crate) fn replace_constructor_payload_for_closure_core_test(
        &mut self,
        constructor: ConstructorId,
        leaf: NominalTypeId,
        donor: NominalTypeId,
    ) -> bool {
        if leaf == donor
            || leaf.module() != donor.module()
            || constructor.owner().module() != leaf.module()
            || self.nominal(leaf).is_none()
            || self.nominal(donor).is_none()
            || self
                .nominal_parameters(leaf)
                .is_none_or(|parameters| !parameters.is_empty())
            || self
                .nominal_parameters(donor)
                .is_none_or(|parameters| !parameters.is_empty())
        {
            return false;
        }
        let Some(position) = self.constructor_positions.get(&constructor).copied() else {
            return false;
        };
        let Some(fact) = self.constructors.get_mut(position) else {
            return false;
        };
        if fact.id != constructor
            || fact.owner != constructor.owner()
            || fact.payload.as_ref() != Some(&Type::Nominal(leaf))
        {
            return false;
        }
        fact.payload = Some(Type::Nominal(donor));
        true
    }
}

#[test]
fn checked_constructor_closure_summary_work_is_exact_and_operation_local() {
    let summary = summary();
    assert_payload_only_leaf(&summary);
    let mut work = TypeWorkBudget::default();
    let mut constraints = crate::interface::InterfaceConstraintBudget::default();
    summary.authenticate(&mut work, &mut constraints).unwrap();
    let (types, interfaces) = (work.used(), constraints.used());
    assert!(types > 7 && interfaces > 7);
    for (type_short, constraint_short) in
        [(false, false), (true, false), (false, true), (false, false)]
    {
        let mut work = TypeWorkBudget::with_limit(7 + types - usize::from(type_short));
        let mut constraints = crate::interface::InterfaceConstraintBudget::with_limit(
            7 + interfaces - usize::from(constraint_short),
        );
        work.charge(7).unwrap();
        constraints.charge(7).unwrap();
        assert_eq!(
            summary.authenticate(&mut work, &mut constraints),
            if type_short {
                Err(ResolvedBuildFailure::TypeResource)
            } else if constraint_short {
                Err(ResolvedBuildFailure::ConstraintResource)
            } else {
                Ok(())
            }
        );
    }
    let mut work = TypeWorkBudget::with_limit(types);
    let mut constraints = crate::interface::InterfaceConstraintBudget::with_limit(interfaces);
    summary.authenticate(&mut work, &mut constraints).unwrap();
    assert!(matches!(
        summary.authenticate(&mut work, &mut constraints),
        Err(ResolvedBuildFailure::TypeResource | ResolvedBuildFailure::ConstraintResource)
    ));
    summary
        .authenticate(
            &mut TypeWorkBudget::with_limit(types),
            &mut crate::interface::InterfaceConstraintBudget::with_limit(interfaces),
        )
        .unwrap();
}
