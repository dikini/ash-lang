use super::checked_wrapper_tests::{WRAPPER_SOURCE, authenticate, wrapper_summary_from_source};
use super::*;

fn selected_summary() -> ExportSummary {
    wrapper_summary_from_source(&format!(
        "{}{}",
        WRAPPER_SOURCE.replace("pub closed", "closed"),
        r#"pub interface Read<A> {
    read : A -> Foreign.CheckedCall<Int>
}
pub impl Read<Int> {
    read value = closed value
}
"#
    ))
}

#[test]
fn checked_selected_method_control_retains_native_assumptions() {
    let summary = selected_summary();
    authenticate(&summary).unwrap();
    assert_eq!(summary.implementations.len(), 1);
    assert_eq!(summary.implementations[0].fact.methods.len(), 1);
    assert_eq!(summary.native_symbols.len(), 1);
    assert!(
        summary.terms.is_empty(),
        "only selected method reaches native work"
    );
    assert!(
        summary
            .requires_checked_foreign_profile(&mut TypeWorkBudget::unbounded())
            .unwrap()
    );
    let symbol = summary.native_symbols.values().next().unwrap();
    assert!(
        !symbol.prepared().checked_contract().unwrap().symbols()[0]
            .minimum_assumptions()
            .is_empty()
    );
}

#[test]
fn checked_selected_method_rejects_capture_erasure() {
    let mut summary = selected_summary();
    authenticate(&summary).unwrap();
    summary.implementations[0].fact.methods[0].capture =
        crate::core::capture::CaptureValueSummary::default();
    assert!(
        authenticate(&summary).is_err(),
        "selected method capture erasure was accepted"
    );
}

#[test]
fn checked_selected_method_rejects_coordinated_capture_and_native_erasure() {
    let mut summary = selected_summary();
    authenticate(&summary).unwrap();
    summary.implementations[0].fact.methods[0].capture =
        crate::core::capture::CaptureValueSummary::default();
    summary.native_symbols.clear();
    summary
        .effects
        .retain(|effect| effect.native_contract.is_none());
    summary.effect_positions = summary
        .effects
        .iter()
        .enumerate()
        .map(|(index, effect)| (effect.id, index))
        .collect();
    assert!(
        authenticate(&summary).is_err(),
        "coordinated selected method closure erasure was accepted"
    );
}

fn selected_dag_summary() -> ExportSummary {
    wrapper_summary_from_source(&format!(
        "{}{}",
        WRAPPER_SOURCE.replace("pub closed", "closed"),
        r#"pub type Box<A> = Box(A)
pub interface Read<A> {
    read : A -> Foreign.CheckedCall<Int>
}
pub impl Read<Int> {
    read value = closed value
}
pub impl<A> Read<Box<A>> where Read<A> {
    read (Box value) = read value
}
"#
    ))
}

#[test]
fn checked_selected_publication_rejects_absent_donor_stale_and_full_head_changes() {
    let mut summary = selected_summary();
    authenticate(&summary).unwrap();
    summary.implementations[0].publication = None;
    assert!(authenticate(&summary).is_err());

    let donor = selected_summary();
    let mut summary = selected_summary();
    authenticate(&summary).unwrap();
    summary.implementations[0].publication = donor.implementations[0]
        .publication
        .as_ref()
        .map(Arc::clone);
    assert!(
        authenticate(&summary).is_err(),
        "same-shaped donor original was accepted"
    );

    let mut summary = selected_summary();
    authenticate(&summary).unwrap();
    Arc::get_mut(summary.implementations[0].publication.as_mut().unwrap())
        .unwrap()
        .methods[0]
        .capture = crate::core::capture::CaptureValueSummary::default();
    assert!(
        authenticate(&summary).is_err(),
        "stale original capture was accepted"
    );

    let mutations: &[fn(&mut CheckedImplementationFact)] = &[
        |fact| fact.methods[0].head_type_parameter_count += 1,
        |fact| fact.methods[0].binder = BinderId::resolved(fact.id.module(), 9999),
        |fact| {
            fact.application = InterfaceApplication::new(fact.interface(), Box::new([Type::Bool]))
        },
        |fact| {
            fact.prerequisites[0].application =
                InterfaceApplication::new(fact.prerequisites[0].interface(), Box::new([Type::Int]))
        },
    ];
    for (index, mutate) in mutations.iter().enumerate() {
        let mut summary = selected_dag_summary();
        authenticate(&summary).unwrap();
        let selected = &mut summary.implementations[1];
        assert_eq!(selected.fact.prerequisites.len(), 1);
        mutate(&mut selected.fact);
        assert!(
            authenticate_implementation_publication(
                &selected.fact,
                selected.publication.as_ref(),
                &mut TypeWorkBudget::unbounded(),
                &mut crate::interface::InterfaceConstraintBudget::with_limit(usize::MAX)
            )
            .is_err(),
            "original relation mutation {index} was accepted"
        );
    }
}

#[test]
fn checked_selected_publication_comparison_has_exact_prefixed_and_fresh_budgets() {
    let summary = selected_dag_summary();
    authenticate(&summary).unwrap();
    let selected = &summary.implementations[1];
    let mut types = TypeWorkBudget::unbounded();
    let mut constraints = crate::interface::InterfaceConstraintBudget::with_limit(usize::MAX);
    authenticate_implementation_publication(
        &selected.fact,
        selected.publication.as_ref(),
        &mut types,
        &mut constraints,
    )
    .unwrap();
    let (type_used, constraint_used) = (types.used(), constraints.used());
    assert!(type_used > 1 && constraint_used > 1);
    let prefix = 7;
    let mut exact_types = TypeWorkBudget::with_limit(prefix + type_used);
    exact_types.charge(prefix).unwrap();
    let mut exact_constraints =
        crate::interface::InterfaceConstraintBudget::with_limit(prefix + constraint_used);
    exact_constraints.charge(prefix).unwrap();
    authenticate_implementation_publication(
        &selected.fact,
        selected.publication.as_ref(),
        &mut exact_types,
        &mut exact_constraints,
    )
    .unwrap();
    assert_eq!(
        (exact_types.used(), exact_constraints.used()),
        (prefix + type_used, prefix + constraint_used)
    );
    let mut short_types = TypeWorkBudget::with_limit(prefix + type_used - 1);
    short_types.charge(prefix).unwrap();
    assert_eq!(
        authenticate_implementation_publication(
            &selected.fact,
            selected.publication.as_ref(),
            &mut short_types,
            &mut crate::interface::InterfaceConstraintBudget::with_limit(usize::MAX)
        ),
        Err(ResolvedBuildFailure::TypeResource)
    );
    let mut short_constraints =
        crate::interface::InterfaceConstraintBudget::with_limit(prefix + constraint_used - 1);
    short_constraints.charge(prefix).unwrap();
    assert_eq!(
        authenticate_implementation_publication(
            &selected.fact,
            selected.publication.as_ref(),
            &mut TypeWorkBudget::unbounded(),
            &mut short_constraints
        ),
        Err(ResolvedBuildFailure::ConstraintResource)
    );
    authenticate_implementation_publication(
        &selected.fact,
        selected.publication.as_ref(),
        &mut TypeWorkBudget::with_limit(type_used),
        &mut crate::interface::InterfaceConstraintBudget::with_limit(constraint_used),
    )
    .unwrap();
}

#[test]
fn checked_selected_publication_deep_origins_clone_refuse_replace_and_drop_iteratively() {
    let summary = selected_dag_summary();
    let fact = clone_checked_implementation_fact(
        &summary.implementations[1].fact,
        &mut TypeWorkBudget::unbounded(),
        &mut crate::interface::InterfaceConstraintBudget::with_limit(usize::MAX),
    )
    .unwrap();
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let mut fact = fact;
            let deep = |span| {
                let mut origin = Origin::Source(span);
                for _ in 0..32768 {
                    origin = Origin::Generated {
                        cause: Box::new(origin),
                        reason: crate::source::GeneratedReason::TypeChecking,
                    };
                }
                origin
            };
            fact.origin = deep(fact.span);
            fact.methods[0].origin = deep(fact.methods[0].span);
            fact.prerequisites[0].origin = deep(fact.prerequisites[0].span);
            let mut work = TypeWorkBudget::unbounded();
            let cloned = clone_checked_implementation_fact(
                &fact,
                &mut work,
                &mut crate::interface::InterfaceConstraintBudget::with_limit(usize::MAX),
            )
            .unwrap();
            let required = work.used();
            assert!(required > 3 * 32768);
            let mut short = TypeWorkBudget::with_limit(required - 1);
            assert!(matches!(
                clone_checked_implementation_fact(
                    &fact,
                    &mut short,
                    &mut crate::interface::InterfaceConstraintBudget::with_limit(usize::MAX)
                ),
                Err(ResolvedBuildFailure::TypeResource)
            ));
            let original = Arc::new(cloned);
            let shared = Arc::clone(&original);
            drop(original);
            let mut holder = Some(shared);
            let replacement = clone_checked_implementation_fact(
                &fact,
                &mut TypeWorkBudget::with_limit(required),
                &mut crate::interface::InterfaceConstraintBudget::with_limit(usize::MAX),
            )
            .unwrap();
            let displaced = holder.replace(Arc::new(replacement));
            drop(displaced);
            drop(holder);
            drop(fact);
        })
        .unwrap()
        .join()
        .unwrap();
}

fn selected_route_consumer(
    remint_facade: bool,
) -> Result<ResolvedModule, crate::resolve::ResolveModuleError> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-selected-route-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let source = format!(
        "{}{}",
        WRAPPER_SOURCE.replace("pub closed", "closed"),
        r#"pub interface Read<A> {
    read : A -> Foreign.CheckedCall<Int>
}
pub impl Read<Int> {
    read value = closed value
}
"#
    );
    std::fs::write(directory.join("native.ash"), source).unwrap();
    std::fs::write(
        directory.join("facade.ash"),
        "pub import native (Read, read, impl Read)\n",
    )
    .unwrap();
    std::fs::write(directory.join("entry.ash"), "import @builtin.foreign as Foreign\nimport native as Native\nimport native (impl Read)\nimport facade (impl Read)\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = Native.read 7\n").unwrap();
    let graph = crate::module::load_module_graph(
        &directory.join("entry.ash"),
        &crate::module::ModuleRoots::empty(),
    )
    .unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    let mut summaries: Vec<(ModuleId, ExportSummary)> = Vec::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                crate::resolve::DependencyExports::new(
                    edge,
                    &summaries
                        .iter()
                        .find(|(module, _)| *module == edge.target())
                        .unwrap()
                        .1,
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = crate::resolve::resolve_checked_foreign_module(loaded, &dependencies);
        if loaded.id() == graph.entry() {
            return resolved;
        }
        let mut summary = crate::elaborate::check_module(resolved.unwrap())
            .unwrap()
            .into_exports();
        if loaded.source().display_path().ends_with("facade.ash") {
            let original = summaries
                .iter()
                .find(|(_, summary)| !summary.implementations.is_empty())
                .unwrap()
                .1
                .implementations[0]
                .publication
                .as_ref()
                .unwrap();
            assert!(
                Arc::ptr_eq(
                    original,
                    summary.implementations[0].publication.as_ref().unwrap()
                ),
                "re-export must retain the defining allocation"
            );
            if remint_facade {
                let reminted = clone_checked_implementation_fact(
                    &summary.implementations[0].fact,
                    &mut TypeWorkBudget::unbounded(),
                    &mut crate::interface::InterfaceConstraintBudget::with_limit(usize::MAX),
                )
                .unwrap();
                summary.implementations[0].publication = Some(Arc::new(reminted));
                authenticate(&summary).unwrap();
            }
        }
        summaries.push((loaded.id(), summary));
    }
    panic!("consumer module absent")
}

#[test]
fn checked_selected_import_routes_share_original_and_reject_same_fact_reminting() {
    let valid =
        selected_route_consumer(false).expect("canonical alias/re-export routes should resolve");
    assert_eq!(valid.imported_facts().implementations().count(), 1);
    assert!(
        selected_route_consumer(true).is_err(),
        "same-shaped replacement allocation cannot replace defining publication across routes"
    );
}

#[test]
fn checked_selected_resolved_import_still_requires_the_completed_original() {
    let canonical = selected_route_consumer(false).unwrap();
    crate::elaborate::check_module(canonical).expect("real body-free selected consumer must check");
    let mut missing = selected_route_consumer(false).unwrap();
    missing.imported.implementations[0].publication = None;
    assert!(
        crate::elaborate::check_module(missing).is_err(),
        "post-resolution imported original erasure was accepted"
    );
}
