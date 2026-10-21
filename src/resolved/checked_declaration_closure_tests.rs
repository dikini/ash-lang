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

#[test]
fn checked_declaration_closure_nominal_roots_are_paid_and_operation_local() {
    let summary = summary();
    let capture = &summary.terms["select"].capture;
    let mut measured = TypeWorkBudget::default();
    summary
        .authenticate_capture_effect_closure(
            capture,
            &mut crate::core::capture::CaptureGraphVisits::default(),
            &mut OriginalEffectMemo::new(),
            &mut measured,
        )
        .unwrap();
    let required = measured.used();
    assert!(required > 3);
    for short in [false, true, false] {
        let mut work = TypeWorkBudget::with_limit(7 + required - usize::from(short));
        work.charge(7).unwrap();
        let result = summary.authenticate_capture_effect_closure(
            capture,
            &mut crate::core::capture::CaptureGraphVisits::default(),
            &mut OriginalEffectMemo::new(),
            &mut work,
        );
        assert_eq!(
            result,
            if short {
                Err(ResolvedBuildFailure::TypeResource)
            } else {
                Ok(())
            }
        );
    }
    let mut work = TypeWorkBudget::with_limit(required);
    for expected in [Ok(()), Err(ResolvedBuildFailure::TypeResource)] {
        assert_eq!(
            summary.authenticate_capture_effect_closure(
                capture,
                &mut crate::core::capture::CaptureGraphVisits::default(),
                &mut OriginalEffectMemo::new(),
                &mut work,
            ),
            expected
        );
    }
    let mut shared_work = TypeWorkBudget::default();
    let mut visits = crate::core::capture::CaptureGraphVisits::default();
    let mut originals = OriginalEffectMemo::new();
    summary
        .authenticate_capture_effect_closure(capture, &mut visits, &mut originals, &mut shared_work)
        .unwrap();
    let before = shared_work.used();
    summary
        .authenticate_capture_effect_closure(capture, &mut visits, &mut originals, &mut shared_work)
        .unwrap();
    assert!(shared_work.used() > before);
    assert!(shared_work.used() - before < required);
}

#[test]
fn checked_declaration_closure_body_free_consumer_rejects_erased_kind_metadata() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-nominal-consumer-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    std::fs::write(directory.join("native.ash"), GLOBAL_SOURCE).unwrap();
    std::fs::write(directory.join("entry.ash"), "import @builtin.foreign as Foreign\nimport native as Native\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = {\n    let call = Native.select 7\n    call ()\n}\n").unwrap();
    let graph = crate::module::load_module_graph(
        &directory.join("entry.ash"),
        &crate::module::ModuleRoots::empty(),
    )
    .unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    let mut summaries: Vec<ExportSummary> = Vec::new();
    for loaded in graph.modules() {
        if loaded.id() == graph.entry() {
            let canonical_dependencies = loaded
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
                crate::resolve::resolve_checked_foreign_module(loaded, &canonical_dependencies)
                    .unwrap();
            crate::elaborate::check_module(canonical).unwrap();
            let producer = summaries
                .iter_mut()
                .find(|summary| summary.terms.contains_key("select"))
                .unwrap();
            let held = assert_capture_only_held(producer);
            erase_hidden_nominal(producer, held);
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
                other => panic!("expected dependency-summary authentication refusal: {other:?}"),
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

impl ResolvedRegistry {
    pub(crate) fn erase_nominal_for_closure_core_test(&mut self, id: NominalTypeId) -> bool {
        let before = self.nominals.len();
        self.nominals = std::mem::take(&mut self.nominals)
            .into_vec()
            .into_iter()
            .filter(|fact| fact.id != id)
            .collect();
        self.nominal_positions = self
            .nominals
            .iter()
            .enumerate()
            .map(|(index, fact)| (fact.id, index))
            .collect();
        self.constructors = std::mem::take(&mut self.constructors)
            .into_vec()
            .into_iter()
            .filter(|fact| fact.id.owner() != id)
            .collect();
        self.constructor_positions = self
            .constructors
            .iter()
            .enumerate()
            .map(|(index, fact)| (fact.id, index))
            .collect();
        self.nominal_parameters.remove(&id);
        before != self.nominals.len()
    }
}
