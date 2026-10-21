//! Real original-checker views may contain both legacy and checked call codecs.
//! The view and its authentication remain passive; no native call is evaluated.

use super::*;
use crate::{
    module::{ModuleGraph, ModuleRoots},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason},
};
use std::sync::atomic::{AtomicU64, Ordering};

const SOURCE: &str = include_str!("../../tests/fixtures/checked-owner-lifecycle/owner.ash");

fn graph(source: &str) -> ModuleGraph {
    static IDS: AtomicU64 = AtomicU64::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-checked-codec-category-{}-{}",
        std::process::id(),
        IDS.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    std::fs::write(directory.join("entry.ash"), source).unwrap();
    let graph =
        crate::module::load_module_graph(&directory.join("entry.ash"), &ModuleRoots::empty())
            .unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    graph
}

fn resolve_entry(graph: &ModuleGraph) -> Result<ResolvedModule, ResolveModuleError> {
    let mut dependencies_checked = Vec::<CheckedModule>::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(
                    edge,
                    dependencies_checked
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = crate::resolve::resolve_checked_foreign_module(loaded, &dependencies)?;
        if loaded.id() == graph.entry() {
            return Ok(resolved);
        }
        dependencies_checked.push(crate::elaborate::check_module(resolved).unwrap());
    }
    panic!("fixture entry");
}

fn original_view() -> ResolvedRegistry {
    let graph = graph(SOURCE);
    let resolved = resolve_entry(&graph).expect(
        "canonical lifecycle source resolves without checking or executing lifecycle bodies",
    );
    resolved
        .registry()
        .source_original_checker_view(resolved.imported_facts(), &mut TypeWorkBudget::default())
        .unwrap()
}

fn assert_distinct_original_codecs(view: &ResolvedRegistry) {
    assert_eq!(view.native_symbols.len(), 2);
    assert_eq!(view.scalar_preflights.len(), 10);
    let checked = view.native_symbols.values().next().unwrap().call_codec();
    let legacy = view.scalar_preflights.values().next().unwrap().call_codec();
    assert_eq!(
        checked.module(),
        legacy.module(),
        "both exact codec originals originate in the same builtin Foreign module"
    );
    assert_eq!(checked.ids().call, NominalTypeId::new(checked.module(), 12));
    assert_eq!(legacy.ids().call, NominalTypeId::new(legacy.module(), 1));
    assert_ne!(checked.ids().call, legacy.ids().call);
    for symbol in view.native_symbols.values() {
        assert_eq!(symbol.call_codec().ids(), checked.ids());
    }
    for preflight in view.scalar_preflights.values() {
        assert_eq!(preflight.call_codec().ids(), legacy.ids());
    }
}

#[test]
fn checked_codec_category_real_original_view_accepts_both_call_identities() {
    let view = original_view();
    assert_distinct_original_codecs(&view);
    view.authenticate_provider_contracts(&mut TypeWorkBudget::default())
        .expect("real original view must authenticate legacy preflight and checked native codecs independently");
}

#[test]
fn checked_codec_category_authentication_has_exact_prefix_spent_and_fresh_limits() {
    let view = original_view();
    assert_distinct_original_codecs(&view);
    let mut measured = TypeWorkBudget::default();
    view.authenticate_provider_contracts(&mut measured)
        .expect("canonical category authentication before budget controls");
    let cost = measured.used();
    assert!(cost > 0);
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        view.authenticate_provider_contracts(&mut exact).unwrap();
        assert_eq!(exact.used(), prefix + cost);
        assert_eq!(
            view.authenticate_provider_contracts(&mut exact),
            Err(ResolvedBuildFailure::TypeResource)
        );
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            view.authenticate_provider_contracts(&mut short),
            Err(ResolvedBuildFailure::TypeResource)
        );
    }
    for _ in 0..2 {
        let mut fresh = TypeWorkBudget::with_limit(cost);
        view.authenticate_provider_contracts(&mut fresh).unwrap();
        assert_eq!(fresh.used(), cost);
    }
}

#[test]
fn checked_codec_category_does_not_accept_a_legacy_outer_call_for_checked_teardown() {
    resolve_entry(&graph(SOURCE))
        .expect("unchanged checked symbol must bind before testing its outer codec mutation");
    let before = "State<H, R> -> Foreign.CheckedCall<Foreign.Disposition<Unit>>";
    assert_eq!(SOURCE.matches(before).count(), 1);
    let changed = SOURCE.replace(
        before,
        "State<H, R> -> Foreign.Call<Foreign.Disposition<Unit>>",
    );
    let graph = graph(&changed);
    let entry = graph.module(graph.entry()).unwrap();
    crate::foreign::source_contract::prepare_checked_foreign_library(
        entry.id(),
        &entry.surface().foreign_libraries[0],
    )
    .expect("passive ABI preparation alone cannot establish the resolved outer codec identity");
    let error = resolve_entry(&graph)
        .expect_err("checked source binding must reject the parsed legacy outer Call");
    assert!(
        matches!(error, ResolveModuleError::Resolution(ref diagnostic) if diagnostic.reason == ResolveReason::ForeignContract),
        "expected exact binding refusal, not a resource or syntax failure: {error:?}"
    );
}
