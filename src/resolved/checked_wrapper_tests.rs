use super::*;

const WRAPPER_SOURCE: &str = r#"import @builtin.foreign as Foreign
foreign checked library Native {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    assumption Callee "the admitted native contract holds"
    symbol Abs<H> : Int -> Foreign.CheckedCall<Int> {
        name "abs"
        abi (I32) -> I32
        host H
        assumes { Callee }
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
pub closed<T> : T -> Foreign.CheckedCall<Int>
closed unused = foreign host Local {
    perform Abs<Local>.call 1
}
"#;

fn wrapper_summary() -> ExportSummary {
    wrapper_summary_from_source(WRAPPER_SOURCE)
}

fn wrapper_summary_from_source(source: &str) -> ExportSummary {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-wrapper-summary-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let entry = directory.join("entry.ash");
    std::fs::write(&entry, source).unwrap();
    let graph =
        crate::module::load_module_graph(&entry, &crate::module::ModuleRoots::empty()).unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    let mut checked: Vec<CheckedModule> = Vec::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                crate::resolve::DependencyExports::new(
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
        let resolved =
            crate::resolve::resolve_checked_foreign_module(loaded, &dependencies).unwrap();
        checked.push(crate::elaborate::check_module(resolved).unwrap());
    }
    checked.pop().unwrap().into_exports()
}

fn authenticate(summary: &ExportSummary) -> Result<(), ResolvedBuildFailure> {
    summary.authenticate(
        &mut TypeWorkBudget::unbounded(),
        &mut crate::interface::InterfaceConstraintBudget::with_limit(usize::MAX),
    )
}

#[test]
fn checked_wrapper_summary_keeps_original_contract_and_charges_the_profile_scan() {
    let summary = wrapper_summary();
    authenticate(&summary).unwrap();
    assert_eq!(summary.native_symbols.len(), 1);
    let original = summary.native_symbols.values().next().unwrap();
    let contract = original.prepared().checked_contract().unwrap();
    assert_eq!(contract.assumptions().len(), 1);
    assert_eq!(contract.symbols()[0].assumption_members().len(), 1);
    assert!(!contract.symbols()[0].minimum_assumptions().is_empty());
    let mut measured = TypeWorkBudget::unbounded();
    assert!(
        summary
            .requires_checked_foreign_profile(&mut measured)
            .unwrap()
    );
    let required = measured.used();
    assert_eq!(required, 1);
    let prefix = 7;
    let mut exact = TypeWorkBudget::with_limit(prefix + required);
    exact.charge(prefix).unwrap();
    assert!(
        summary
            .requires_checked_foreign_profile(&mut exact)
            .unwrap()
    );
    let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
    short.charge(prefix).unwrap();
    assert!(matches!(
        summary.requires_checked_foreign_profile(&mut short),
        Err(ResolvedBuildFailure::TypeResource)
    ));
    assert!(
        summary
            .requires_checked_foreign_profile(&mut TypeWorkBudget::with_limit(required))
            .unwrap()
    );
}

#[test]
fn checked_wrapper_summary_rejects_erased_native_and_capture_requirements() {
    let mutations: &[fn(&mut ExportSummary)] = &[
        |summary| summary.terms.get_mut("closed").unwrap().publication = None,
        |summary| summary.native_symbols.clear(),
        |summary| {
            summary
                .effects
                .iter_mut()
                .filter(|effect| effect.native_contract.is_some())
                .for_each(|effect| effect.native_contract = None);
        },
        |summary| summary.erase_exported_capture_for_test("closed"),
        |summary| {
            summary.native_symbols.clear();
            for effect in &mut summary.effects {
                effect.native_contract = None;
            }
        },
        |summary| {
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
        },
        |summary| {
            summary.erase_exported_capture_for_test("closed");
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
        },
    ];
    for (index, mutate) in mutations.iter().enumerate() {
        let mut summary = wrapper_summary();
        authenticate(&summary).unwrap();
        mutate(&mut summary);
        assert!(
            authenticate(&summary).is_err(),
            "erasure {index} was accepted"
        );
    }
}

#[test]
fn checked_wrapper_publication_rejects_donor_and_stale_originals() {
    let donor = wrapper_summary();
    let mut summary = wrapper_summary();
    authenticate(&summary).unwrap();
    summary.terms.get_mut("closed").unwrap().publication =
        donor.terms["closed"].publication.as_ref().map(Arc::clone);
    assert!(
        authenticate(&summary).is_err(),
        "a separately checked original cannot replace the defining binder"
    );
    let mut summary = wrapper_summary();
    let original = summary
        .terms
        .get_mut("closed")
        .unwrap()
        .publication
        .as_mut()
        .unwrap();
    Arc::get_mut(original).unwrap().capture = crate::core::capture::CaptureValueSummary::default();
    assert!(
        authenticate(&summary).is_err(),
        "a stale same-binder capture cannot replace the completed original"
    );
}

#[test]
fn checked_wrapper_publication_comparison_has_a_prefixed_exact_work_boundary() {
    let summary = wrapper_summary();
    let global = &summary.terms["closed"];
    let mut work = TypeWorkBudget::unbounded();
    let mut constraints = crate::interface::InterfaceConstraintBudget::with_limit(usize::MAX);
    authenticate_global_publication(global, &mut work, &mut constraints).unwrap();
    let required = work.used();
    let constraint_required = constraints.used();
    assert!(required > 1 && constraint_required > 0);
    for short in [false, true, false] {
        let prefix = 7;
        let mut work = TypeWorkBudget::with_limit(prefix + required - usize::from(short));
        work.charge(prefix).unwrap();
        let result = authenticate_global_publication(
            global,
            &mut work,
            &mut crate::interface::InterfaceConstraintBudget::with_limit(constraint_required),
        );
        if short {
            assert_eq!(result, Err(ResolvedBuildFailure::TypeResource));
        } else {
            result.unwrap();
        }
    }
    assert_eq!(
        authenticate_global_publication(
            global,
            &mut TypeWorkBudget::with_limit(required),
            &mut crate::interface::InterfaceConstraintBudget::with_limit(constraint_required - 1)
        ),
        Err(ResolvedBuildFailure::ConstraintResource)
    );
}

#[test]
fn checked_wrapper_import_requires_the_same_original_allocation() {
    let summary = wrapper_summary();
    let exported = &summary.terms["closed"];
    let mut imported = ImportedGlobalScheme {
        publication: exported.publication.as_ref().map(Arc::clone),
        scalar_preflight: None,
        capture: exported.capture.clone(),
        binder: exported.binder,
        scheme: exported
            .scheme
            .clone_with_budget(&mut TypeWorkBudget::unbounded())
            .unwrap(),
        origin: exported.origin.clone(),
    };
    let compare = |imported: &ImportedGlobalScheme| {
        same_imported_global_fact_with_budget(
            imported,
            exported,
            &mut TypeWorkBudget::unbounded(),
            &mut crate::interface::InterfaceConstraintBudget::with_limit(usize::MAX),
        )
    };
    assert_eq!(compare(&imported), Ok(true));
    // A newly minted same-shape fact is not the original imported publication.
    imported.publication = None;
    imported = imported.with_fixture_publication();
    assert_eq!(compare(&imported), Ok(false));
}

#[test]
fn checked_wrapper_shared_origin_teardown_is_iterative_on_success_and_refusal() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let source = crate::source::SourceFile::new("shared-wrapper-origin", "x").unwrap();
            let span = source
                .span(crate::source::ByteRange::new(0, 1).unwrap())
                .unwrap();
            let binder = BinderId::resolved(ModuleId::new(10999), 0);
            let fact = || {
                let mut origin = Origin::Source(span);
                for _ in 0..32768 {
                    origin = Origin::Generated {
                        cause: Box::new(origin),
                        reason: crate::source::GeneratedReason::TypeChecking,
                    };
                }
                ImportedGlobalScheme {
                    publication: None,
                    scalar_preflight: None,
                    capture: crate::core::capture::CaptureValueSummary::default(),
                    binder,
                    scheme: ConstrainedScheme::from_rank1_type(Type::Unit),
                    origin,
                }
                .with_fixture_publication()
            };
            let original = fact();
            let retained = original.publication.as_ref().map(Arc::clone);
            discard_imported_global(original);
            drop(retained); // Last shared owner, after the projection has gone.
            let mut imported = ImportedFacts::default();
            assert!(
                imported
                    .insert_global(fact(), &mut TypeWorkBudget::with_limit(0))
                    .is_err()
            );
            assert_eq!(imported.globals.len(), 0);
            imported
                .insert_global(fact(), &mut TypeWorkBudget::unbounded())
                .unwrap();
            imported
                .insert_global(fact(), &mut TypeWorkBudget::unbounded())
                .unwrap();
            drop(imported); // Replacement and final retained original both use iterative teardown.
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn checked_wrapper_aliases_share_one_original_and_reject_replacement() {
    let mut summary = wrapper_summary();
    let source = &summary.terms["closed"];
    let alias = ExportedGlobal {
        publication: source.publication.as_ref().map(Arc::clone),
        scalar_preflight: None,
        capture: source.capture.clone(),
        binder: source.binder,
        scheme: source
            .scheme
            .clone_with_budget(&mut TypeWorkBudget::unbounded())
            .unwrap(),
        origin: source.origin.clone(),
    };
    summary.terms.insert("renamed".to_owned(), alias);
    summary.term_order.push("renamed".to_owned());
    authenticate(&summary).unwrap();
    assert_eq!(
        summary.terms["renamed"]
            .publication
            .as_ref()
            .unwrap()
            .spelling,
        "closed"
    );
    summary.terms.get_mut("renamed").unwrap().capture =
        crate::core::capture::CaptureValueSummary::default();
    assert!(
        authenticate(&summary).is_err(),
        "an alias cannot erase capture while retaining the original allocation"
    );
    summary.terms.get_mut("renamed").unwrap().capture = summary.terms["closed"].capture.clone();
    let mut alias = summary.terms.remove("renamed").unwrap();
    alias.publication = None;
    alias = alias.with_fixture_publication();
    summary.terms.insert("renamed".to_owned(), alias);
    assert!(
        authenticate(&summary).is_err(),
        "same-binder aliases cannot mint another original"
    );
}

#[test]
fn checked_wrapper_branch_and_callable_paths_preserve_original_contract_union() {
    let other = r#"    assumption OtherCallee "the other admitted contract holds"
    symbol Other<H> : Int -> Foreign.CheckedCall<Int> {
        name "abs"
        abi (I32) -> I32
        host H
        assumes { OtherCallee }
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
"#;
    let library = WRAPPER_SOURCE.replace("}\npub closed", &format!("{other}}}\npub closed"));
    let branch = |callee| {
        format!(
            "{library}pub choose : Bool -> Foreign.CheckedCall<Int>\nchoose first = foreign host Local {{\n    match first {{\n        true => perform Abs<Local>.call 1\n        false => perform {callee}<Local>.call 2\n    }}\n}}\n"
        )
    };
    let without_other = wrapper_summary_from_source(&branch("Abs"));
    authenticate(&without_other).unwrap();
    assert_eq!(
        without_other.native_symbols.len(),
        1,
        "an unused private symbol supplies no branch requirement"
    );
    let summary = wrapper_summary_from_source(&branch("Other"));
    authenticate(&summary).unwrap();
    assert_eq!(summary.native_symbols.len(), 2);
    let mut authored = HashSet::new();
    let mut operations = HashSet::new();
    for (operation, symbol) in &summary.native_symbols {
        operations.insert(*operation);
        let prepared = symbol.prepared();
        let contract = prepared.checked_contract().unwrap();
        let member = prepared.symbols()[symbol.symbol_index()].member_index();
        let role = contract
            .symbols()
            .iter()
            .find(|role| role.member_index() == member)
            .unwrap();
        assert!(!role.minimum_assumptions().is_empty());
        for member in role.assumption_members() {
            let assumption = contract
                .assumptions()
                .iter()
                .find(|assumption| assumption.member_index() == *member)
                .unwrap();
            authored.insert(assumption.name().to_owned());
        }
    }
    assert_eq!(operations.len(), 2);
    assert_eq!(
        authored,
        HashSet::from(["Callee".to_owned(), "OtherCallee".to_owned()])
    );
    for wrapper in [
        "pub repeat : Int -> Foreign.CheckedCall<Int>\nrepeat count = match count == 0 {\n    true => closed count\n    false => repeat 0\n}\n",
        "pub select : Bool -> (Int -> Foreign.CheckedCall<Int>)\nselect first = match first {\n    true => closed\n    false => fn(value) {\n        closed value\n    }\n}\n",
    ] {
        let summary = wrapper_summary_from_source(&format!(
            "{}{wrapper}",
            WRAPPER_SOURCE.replace("pub closed", "closed")
        ));
        authenticate(&summary).unwrap();
        assert_eq!(summary.native_symbols.len(), 1);
        assert!(
            summary
                .requires_checked_foreign_profile(&mut TypeWorkBudget::unbounded())
                .unwrap()
        );
    }
}

#[test]
fn checked_wrapper_capture_closure_has_exact_prefixed_and_memoized_work() {
    let summary = wrapper_summary();
    let capture = &summary.terms["closed"].capture;
    let mut measured = TypeWorkBudget::unbounded();
    summary
        .authenticate_capture_effect_closure(
            capture,
            &mut crate::core::capture::CaptureGraphVisits::default(),
            &mut measured,
        )
        .unwrap();
    let required = measured.used();
    assert!(required > 2);
    for short in [false, true, false] {
        let mut work = TypeWorkBudget::with_limit(7 + required - usize::from(short));
        work.charge(7).unwrap();
        let mut visits = crate::core::capture::CaptureGraphVisits::default();
        let result = summary.authenticate_capture_effect_closure(capture, &mut visits, &mut work);
        if short {
            assert_eq!(result, Err(ResolvedBuildFailure::TypeResource));
        } else {
            result.unwrap();
        }
    }
    let mut visits = crate::core::capture::CaptureGraphVisits::default();
    let mut work = TypeWorkBudget::with_limit(required + 1);
    summary
        .authenticate_capture_effect_closure(capture, &mut visits, &mut work)
        .unwrap();
    summary
        .authenticate_capture_effect_closure(capture, &mut visits, &mut work)
        .unwrap();
    assert_eq!(
        work.used(),
        required + 1,
        "an alias pays its visit while sharing the complete graph scan"
    );
}
