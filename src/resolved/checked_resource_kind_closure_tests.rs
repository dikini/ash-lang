//! Real source-resource family kinds in capture closure, without native execution.

use super::checked_wrapper_tests::{capture_kinds_for_test, capture_kinds_without_for_test};
use super::*;

fn source_control_summary() -> ExportSummary {
    let entry = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/source-owner/control_capture.ash");
    let graph = crate::module::load_module_graph(&entry, &crate::module::ModuleRoots::empty())
        .expect("actual source-owner fixture module graph");
    let mut checked: Vec<CheckedModule> = Vec::new();
    let mut availability = crate::elaborate::ProviderCodeAvailability::default();
    // Match the modular driver's paid source phase, not the separate fixed
    // image/startup allowance. Keep each rewrite arena separately funded.
    let (mut checking, source_bytes) = crate::compiler_work::source_work(&graph)
        .expect("paid normal-driver 800*S source checking census");
    let source_limit = checking.limit();
    checking
        .finish_sizing(crate::calibration::limit(
            source_limit,
            crate::calibration::DiagnosticOwner::Structural,
        ))
        .expect("normal-driver source checking allowance");
    let rewrite_limit = crate::calibration::limit(
        crate::compiler_work::rewrite_total(source_bytes)
            .expect("normal-driver 16*S per-arena rewrite allowance"),
        crate::calibration::DiagnosticOwner::Structural,
    );
    let mut coverage = crate::pattern::UsefulnessBudget::default();
    let mut constraints = crate::interface::InterfaceConstraintBudget::default();
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
        let resolved = crate::resolve::resolve_module(loaded, &dependencies)
            .expect("ordinary source-owner resolution");
        let module = crate::elaborate::check_module_with_budget_and_provider_codes_and_rewrite_work(
            resolved,
            &availability,
            &mut checking,
            &mut coverage,
            &mut constraints,
            Some(TypeWorkBudget::with_limit(rewrite_limit)),
        )
        .expect("source-owner checking with paid dependency code and normal-driver source/rewrite funding");
        if let Some(code) = module.provider_code() {
            availability
                .retain(module.module(), code, &mut checking)
                .expect("retain the checked dependency provider original");
        }
        if let Some(code) = module.source_resource_code() {
            availability
                .retain_source(module.module(), code, &mut checking)
                .expect("retain the checked dependency source-resource original");
        }
        checked.push(module);
    }
    checked.pop().unwrap().into_exports()
}

fn authenticate_default(summary: &ExportSummary) -> Result<(), ResolvedBuildFailure> {
    summary.authenticate(
        &mut TypeWorkBudget::default(),
        &mut crate::interface::InterfaceConstraintBudget::default(),
    )
}

fn probe_family_in_capture(summary: &ExportSummary) -> NominalTypeId {
    let mut probes = summary
        .source_resource_facts
        .values()
        .filter(|fact| fact.id.module() == summary.module && fact.spelling == "Probe");
    let probe = probes.next().expect("actual local source-resource Probe");
    assert!(probes.next().is_none());
    assert_eq!(probe.id.ordinal(), 0);
    assert_eq!(probe.family.module(), summary.module);
    assert!(
        summary.nominal_fact(probe.family).is_none(),
        "resource family is a kind-only identity, not an ordinary nominal fact"
    );
    let mut work = TypeWorkBudget::default();
    let mut captured = HashSet::new();
    for ty in summary.terms["both"].capture.types(&mut work).unwrap() {
        collect_capture_external_nominals(ty, &mut captured, &mut work).unwrap();
    }
    assert!(
        captured.contains(&probe.family),
        "the actual both capture must reference this exact source-resource family"
    );
    probe.family
}

#[test]
fn checked_resource_kind_closure_accepts_actual_kind_only_probe_family() {
    let summary = source_control_summary();
    let family = probe_family_in_capture(&summary);
    authenticate_default(&summary).unwrap();
    let kinds = capture_kinds_for_test(&summary);
    assert!(kinds.contains_nominal(family));
    summary
        .authenticate_capture_effect_closure(
            &summary.terms["both"].capture,
            &kinds,
            &mut crate::core::capture::CaptureGraphVisits::default(),
            &mut OriginalEffectMemo::new(),
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
}

#[test]
fn checked_resource_kind_closure_rejects_exact_missing_probe_kind() {
    let summary = source_control_summary();
    let family = probe_family_in_capture(&summary);
    authenticate_default(&summary).unwrap();
    let capture = &summary.terms["both"].capture;
    let full = capture_kinds_for_test(&summary);
    summary
        .authenticate_capture_effect_closure(
            capture,
            &full,
            &mut crate::core::capture::CaptureGraphVisits::default(),
            &mut OriginalEffectMemo::new(),
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
    // Only the independently supplied test kind input changes. Capture,
    // completed publication, native originals and resource facts stay intact.
    let missing = capture_kinds_without_for_test(&summary, Some(family));
    assert!(!missing.contains_nominal(family));
    assert_eq!(
        summary.authenticate_capture_effect_closure(
            capture,
            &missing,
            &mut crate::core::capture::CaptureGraphVisits::default(),
            &mut OriginalEffectMemo::new(),
            &mut TypeWorkBudget::default()
        ),
        Err(ResolvedBuildFailure::InvalidState),
        "an unknown required resource family cannot receive a blanket exemption"
    );
    authenticate_default(&summary).unwrap();
}
