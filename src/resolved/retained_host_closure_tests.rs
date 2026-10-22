//! Genuine selective legacy facade, retained Host checking dependencies only.
use super::checked_wrapper_tests::wrapper_summary_from_source;
use super::*;
const SOURCE: &str = "pub import @builtin.foreign (checked_i64 as signed)\n";
fn summary() -> ExportSummary {
    wrapper_summary_from_source(SOURCE)
}
fn auth(summary: &ExportSummary, work: &mut TypeWorkBudget) -> Result<(), ResolvedBuildFailure> {
    summary.authenticate(
        work,
        &mut crate::interface::InterfaceConstraintBudget::default(),
    )
}
fn host_module(summary: &ExportSummary) -> ModuleId {
    let hosts = summary
        .effects
        .iter()
        .filter(|e| {
            e.id.module().is_builtin_foreign()
                && e.id.declaration() == crate::module::FOREIGN_NATIVE_HOST_LOCAL
        })
        .collect::<Vec<_>>();
    assert_eq!(hosts.len(), 1, "actual selective capture retains Host");
    hosts[0].id.module()
}
#[test]
fn retained_host_closure_facade_has_only_selected_names_but_full_checking_inventory() {
    let summary = summary();
    auth(&summary, &mut TypeWorkBudget::default()).unwrap();
    let module = host_module(&summary);
    assert_eq!(summary.term_order, ["signed"]);
    assert_eq!(summary.terms.len(), 1);
    assert!(summary.nominals.is_empty());
    assert!(summary.constructors.is_empty());
    assert!(summary.effect_names.is_empty());
    for (id, coords, family) in
        crate::foreign::scalar_preflight::checked_inventory_dependencies(module)
    {
        let fact = summary.nominal_fact(id).unwrap();
        assert_eq!(fact.parameter_count, coords.formals().len());
        assert_eq!(fact.constructor_count, coords.constructors().len());
        if family {
            assert_eq!(fact.constructors.len(), fact.constructor_count);
            for ctor in fact.constructors {
                assert!(summary.constructor_by_id(*ctor).unwrap().original.is_some());
            }
        } else {
            assert!(
                fact.constructors.is_empty(),
                "opaque ConversionError/Extent remain kind-only"
            );
        }
        assert!(!summary.nominal_names_by_id.contains_key(&id));
    }
}
#[test]
fn retained_host_closure_missing_required_nominal_or_constructor_refuses() {
    for constructor in [false, true] {
        let mut summary = summary();
        auth(&summary, &mut TypeWorkBudget::default()).unwrap();
        let module = host_module(&summary);
        let id = NominalTypeId::new(module, 12);
        if constructor {
            let ctor = ConstructorId::new(id, 0);
            summary.hidden_constructors.remove(&ctor).unwrap();
            summary.hidden_constructor_order.retain(|v| *v != ctor);
        } else {
            summary
                .hidden_nominals
                .remove(&id)
                .unwrap()
                .discard_iteratively();
            summary.hidden_nominal_order.retain(|v| *v != id);
        }
        assert_eq!(
            auth(&summary, &mut TypeWorkBudget::default()).unwrap_err(),
            ResolvedBuildFailure::InvalidState
        );
    }
}
#[test]
fn retained_host_closure_same_kind_formal_donor_is_not_original_correspondence() {
    let mut summary = summary();
    auth(&summary, &mut TypeWorkBudget::default()).unwrap();
    let module = host_module(&summary);
    // Output<A> and FinishResult<E> both have one Type formal and two ctors.
    let donor = NominalTypeId::new(module, 2);
    let target = NominalTypeId::new(module, 13);
    let parameters = clone_resolved_type_variable_buffer_with_budget(
        &summary.hidden_nominals[&donor].parameters,
        &mut TypeWorkBudget::default(),
    )
    .unwrap()
    .into_boxed_slice();
    let target = summary.hidden_nominals.get_mut(&target).unwrap();
    assert_eq!(target.parameters.len(), parameters.len());
    assert_ne!(target.parameters[0].id, parameters[0].id);
    target.parameters = parameters;
    assert_eq!(
        auth(&summary, &mut TypeWorkBudget::default()).unwrap_err(),
        ResolvedBuildFailure::InvalidState
    );
}
#[test]
fn retained_host_closure_auth_has_exact_prefix_short_spent_and_fresh_work() {
    let summary = summary();
    let mut measured = TypeWorkBudget::default();
    auth(&summary, &mut measured).unwrap();
    let cost = measured.used();
    assert!(cost > 0);
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        auth(&summary, &mut exact).unwrap();
        assert_eq!(exact.used(), prefix + cost);
        assert_eq!(
            auth(&summary, &mut exact).unwrap_err(),
            ResolvedBuildFailure::TypeResource
        );
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            auth(&summary, &mut short).unwrap_err(),
            ResolvedBuildFailure::TypeResource
        );
    }
    for _ in 0..2 {
        auth(&summary, &mut TypeWorkBudget::with_limit(cost)).unwrap();
    }
}

#[test]
fn retained_host_closure_ordinary_selective_direct_and_facade_linked_core_still_validate() {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    struct Owned(std::path::PathBuf);
    impl Drop for Owned {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    for facade in [false, true] {
        let owned = loop {
            let p = std::env::temp_dir().join(format!(
                "ash-host-closure-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&p) {
                Ok(()) => break Owned(p),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("owned fixture {e}"),
            }
        };
        std::fs::write(owned.0.join("facade.ash"), SOURCE).unwrap();
        let text = if facade {
            "import facade (signed as selected)\nmain : Unit -> Int\nmain () = 42\n"
        } else {
            "import @builtin.foreign (checked_i64 as selected)\nmain : Unit -> Int\nmain () = 42\n"
        };
        let entry = owned.0.join("entry.ash");
        std::fs::write(&entry, text).unwrap();
        let compiled = crate::driver::compile_path(crate::driver::RunConfiguration {
            entry,
            roots: crate::module::ModuleRoots::empty(),
        })
        .expect("ordinary selective source/summary/link pipeline before independent Core");
        if let Some((program, provenance)) = compiled.effect_build_input() {
            let sources = provenance
                .iter()
                .map(|(_, s)| s.as_ref())
                .collect::<Vec<_>>();
            let modules = provenance
                .iter()
                .map(|(m, s)| (*m, s.id()))
                .collect::<Vec<_>>();
            for transformed in [
                crate::core::transform::identity_effect_traversal(program).unwrap(),
                crate::core::transform::fold_effect_literal_primitives(program).unwrap(),
            ] {
                crate::core::validate_effect_modules(transformed, &sources, &modules)
                    .expect("ordinary linked Effect Core remains independent");
            }
        } else {
            let (program, provenance) = compiled
                .pure_build_input()
                .expect("actual compiler produces one Core dialect");
            let sources = provenance
                .iter()
                .map(|(_, s)| s.as_ref())
                .collect::<Vec<_>>();
            let modules = provenance
                .iter()
                .map(|(m, s)| (*m, s.id()))
                .collect::<Vec<_>>();
            for transformed in [
                crate::core::transform::identity_traversal(program).unwrap(),
                crate::core::transform::fold_literal_primitives(program).unwrap(),
            ] {
                crate::core::validate_modules(transformed, &sources, &modules)
                    .expect("ordinary linked Pure Core remains independent");
            }
        }
    }
}
