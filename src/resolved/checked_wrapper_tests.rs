use super::*;

fn wrapper_summary() -> ExportSummary {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-wrapper-summary-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let entry = directory.join("entry.ash");
    std::fs::write(
        &entry,
        r#"import @builtin.foreign as Foreign
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
"#,
    )
    .unwrap();
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
