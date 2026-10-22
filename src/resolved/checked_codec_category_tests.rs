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
    assert_eq!(view.scalar_preflights.len(), 14);
    let checked = view.native_symbols.values().next().unwrap().call_codec();
    let legacy = view
        .scalar_preflights
        .values()
        .find(|fact| fact.role().host_parameter(fact.module()).is_none())
        .unwrap()
        .call_codec();
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
        assert_eq!(
            preflight.call_codec().ids(),
            if preflight
                .role()
                .host_parameter(preflight.module())
                .is_some()
            {
                checked.ids()
            } else {
                legacy.ids()
            }
        );
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

#[test]
fn checked_memory_preflight_codecs_keep_exact_family_originals() {
    let view = original_view();
    view.authenticate_scalar_preflights(&mut TypeWorkBudget::default())
        .expect("genuine original preflight table authenticates before pointer mutations");
    let module = view.scalar_preflights.values().next().unwrap().module();
    let legacy = &view.scalar_preflights[&BinderId::resolved(module, 0)];
    let checked = &view.scalar_preflights[&BinderId::resolved(module, 11)];
    assert_ne!(
        legacy.call_codec().ids().call,
        checked.call_codec().ids().call
    );
    for fact in view.scalar_preflights.values() {
        let expected = if fact.role().host_parameter(module).is_some() {
            checked
        } else {
            legacy
        };
        assert!(Arc::ptr_eq(fact.call_codec(), expected.call_codec()));
    }
    for local in [2, 14] {
        let mut candidate = original_view();
        // Each graph has its own admitted module identity: select the genuine
        // defining function from this candidate rather than transplanting IDs.
        let function = candidate
            .scalar_preflights
            .keys()
            .find(|id| id.local() == local)
            .copied()
            .unwrap();
        let fact = Arc::clone(&candidate.scalar_preflights[&function]);
        let mut work = TypeWorkBudget::default();
        let codec = crate::foreign::checked_source::CheckedForeignCallCodec::authenticate(
            fact.module(),
            fact.source(),
            fact.call_codec().ids(),
            &candidate,
            &mut work,
        )
        .unwrap();
        let reminted = crate::foreign::scalar_preflight::CheckedForeignScalarPreflight::from_original(
            fact.role(), fact.source(), fact.origin(), fact.annotation(), Arc::new(codec), &mut work,
        ).expect("same defining shape is valid independently; original pointer continuity must still refuse");
        reminted
            .authenticate(&candidate, &mut TypeWorkBudget::default())
            .expect("the reminted fact is independently valid before family continuity rejects it");
        candidate
            .scalar_preflights
            .insert(function, Arc::new(reminted));
        assert_eq!(
            candidate.authenticate_scalar_preflights(&mut TypeWorkBudget::default()),
            Err(ResolvedBuildFailure::InvalidState)
        );
        view.authenticate_scalar_preflights(&mut TypeWorkBudget::default())
            .unwrap();
    }
}

#[test]
fn checked_memory_scheme_kinds_require_exact_complete_original_formals() {
    let view = original_view();
    let donor = original_view();
    let donor_module = donor.scalar_preflights.values().next().unwrap().module();
    view.authenticate_scalar_preflights(&mut TypeWorkBudget::default())
        .unwrap();
    for (_, fact) in view.scalar_preflights() {
        let Type::Forall(parameters, _) = fact.core_signature() else {
            continue;
        };
        assert!(fact.matches_parameters(parameters));
        for (identity, expected) in parameters {
            let mut measured = TypeWorkBudget::default();
            assert_eq!(
                fact.parameter_kind_with_charge(*identity, |n| measured.charge(n))
                    .unwrap(),
                Some(expected)
            );
            let cost = measured.used();
            assert_eq!(cost, parameters.len());
            for prefix in [0, 7] {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                assert_eq!(
                    fact.parameter_kind_with_charge(*identity, |n| exact.charge(n))
                        .unwrap(),
                    Some(expected)
                );
                assert_eq!(exact.used(), prefix + cost);
                assert!(
                    fact.parameter_kind_with_charge(*identity, |n| exact.charge(n))
                        .is_err()
                );
                let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.charge(prefix).unwrap();
                assert!(
                    fact.parameter_kind_with_charge(*identity, |n| short.charge(n))
                        .is_err()
                );
            }
            for _ in 0..2 {
                let mut fresh = TypeWorkBudget::with_limit(cost);
                assert_eq!(
                    fact.parameter_kind_with_charge(*identity, |n| fresh.charge(n))
                        .unwrap(),
                    Some(expected)
                );
            }
        }
        // Same spelling/local number in another module is not this declaration.
        for unknown in [
            TypeVariableId::resolved(fact.module(), 999),
            TypeVariableId::resolved(ModuleId::new(999), 23),
            TypeVariableId::resolved(donor_module, 23),
            TypeVariableId::Generated(999),
        ] {
            let mut work = TypeWorkBudget::default();
            assert_eq!(
                fact.parameter_kind_with_charge(unknown, |n| work.charge(n))
                    .unwrap(),
                None
            );
        }
    }
}

#[test]
fn checked_memory_family_authentication_rechecks_each_fresh_registry_and_budget() {
    let view = original_view();
    let mut measured = TypeWorkBudget::default();
    view.authenticate_scalar_preflights(&mut measured).unwrap();
    let cost = measured.used();
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        view.authenticate_scalar_preflights(&mut exact).unwrap();
        assert_eq!(exact.used(), prefix + cost);
        assert_eq!(
            view.authenticate_scalar_preflights(&mut exact),
            Err(ResolvedBuildFailure::TypeResource)
        );
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            view.authenticate_scalar_preflights(&mut short),
            Err(ResolvedBuildFailure::TypeResource)
        );
    }
    let module = view.scalar_preflights.values().next().unwrap().module();
    for local in [0, 11] {
        let mut changed = view.clone();
        changed
            .scalar_preflights
            .remove(&BinderId::resolved(module, local))
            .unwrap();
        assert_eq!(
            changed.authenticate_scalar_preflights(&mut TypeWorkBudget::default()),
            Err(ResolvedBuildFailure::InvalidState)
        );
    }
    for change in 0..3 {
        let mut changed = view.clone();
        if change == 0 {
            changed
                .effects
                .iter_mut()
                .find(|effect| {
                    effect.id
                        == crate::types::EffectId::new(
                            module,
                            crate::module::FOREIGN_NATIVE_HOST_LOCAL,
                        )
                })
                .unwrap()
                .public = false;
        } else if change == 1 {
            changed
                .constructors
                .iter_mut()
                .find(|ctor| {
                    ctor.id
                        == crate::types::ConstructorId::new(
                            crate::types::NominalTypeId::new(module, 12),
                            2,
                        )
                })
                .unwrap()
                .payload = Some(Type::Int);
        } else {
            let fact = changed
                .scalar_preflights
                .remove(&BinderId::resolved(module, 14))
                .unwrap();
            changed
                .scalar_preflights
                .insert(BinderId::resolved(module, 999), fact);
        }
        for _ in 0..2 {
            assert_eq!(
                changed.authenticate_scalar_preflights(&mut TypeWorkBudget::default()),
                Err(ResolvedBuildFailure::InvalidState)
            );
            let mut fresh = TypeWorkBudget::with_limit(cost);
            view.authenticate_scalar_preflights(&mut fresh).unwrap();
            assert_eq!(fresh.used(), cost);
        }
    }
}

#[test]
fn checked_memory_family_proofs_are_distinct_across_genuine_builtin_graphs() {
    fn completed() -> Vec<CheckedModule> {
        let graph = graph("import @builtin.foreign as Foreign\nmain : Unit -> Int\nmain () = 42\n");
        let mut checked = Vec::<CheckedModule>::new();
        for loaded in graph.modules() {
            let dependencies = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    DependencyExports::new(
                        edge,
                        checked
                            .iter()
                            .find(|m| m.module() == edge.target())
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
        checked
    }
    let mut checked = completed();
    checked.extend(completed());
    let view = ResolvedRegistry::combine_checked(
        &checked,
        &mut TypeWorkBudget::default(),
        &mut crate::interface::InterfaceConstraintBudget::default(),
    )
    .unwrap();
    view.authenticate_scalar_preflights(&mut TypeWorkBudget::default())
        .expect("both genuine graph families authenticate together before the mutation");
    let first = view
        .scalar_preflights()
        .find(|(_, fact)| fact.role().host_parameter(fact.module()).is_some())
        .unwrap()
        .1
        .module();
    let second = view
        .scalar_preflights()
        .find(|(_, fact)| {
            fact.role().host_parameter(fact.module()).is_some() && fact.module() != first
        })
        .unwrap()
        .1
        .module();
    assert_ne!(first, second);

    // A checked proof for the first graph cannot cover an unlisted checked
    // family in the second graph, even though its legacy table is valid.
    let mut uncovered = view.clone();
    uncovered
        .scalar_preflights
        .retain(|_, fact| fact.module() != second || fact.role().host_parameter(second).is_none());
    let scalar = uncovered
        .authenticate_scalar_preflights_for_owners(&mut TypeWorkBudget::default())
        .unwrap();
    let proof = uncovered
        .authenticate_owner_definitions_with_preflights(scalar, &mut TypeWorkBudget::default())
        .unwrap();
    let second_host = uncovered
        .effect(crate::types::EffectId::new(second, 0))
        .unwrap();
    let mut full = TypeWorkBudget::default();
    assert!(
        crate::foreign::checked_builtins::is_canonical_native_host(
            second_host,
            &uncovered,
            &mut full
        )
        .unwrap()
    );
    let mut fallback = TypeWorkBudget::default();
    assert!(
        proof
            .is_canonical_native_host(second_host, &uncovered, &mut fallback)
            .unwrap()
    );
    assert!(fallback.used() >= full.used());
    let mut malformed = uncovered.clone();
    let boundary =
        crate::types::ConstructorId::new(crate::types::NominalTypeId::new(second, 12), 2);
    malformed
        .constructors
        .iter_mut()
        .find(|row| row.id == boundary)
        .unwrap()
        .payload = Some(Type::Unit);
    let scalar = malformed
        .authenticate_scalar_preflights_for_owners(&mut TypeWorkBudget::default())
        .expect("independent first checked family and second legacy family remain valid");
    let proof = malformed
        .authenticate_owner_definitions_with_preflights(scalar, &mut TypeWorkBudget::default())
        .unwrap();
    let second_host = malformed
        .effect(crate::types::EffectId::new(second, 0))
        .unwrap();
    assert!(
        !proof
            .is_canonical_native_host(second_host, &malformed, &mut TypeWorkBudget::default())
            .unwrap()
    );
    let mut changed = view.clone();
    changed
        .constructors
        .iter_mut()
        .find(|ctor| {
            ctor.id
                == crate::types::ConstructorId::new(crate::types::NominalTypeId::new(second, 12), 2)
        })
        .unwrap()
        .payload = Some(Type::Int);
    assert_eq!(
        changed
            .scalar_preflights()
            .find(|(_, fact)| fact.role().host_parameter(fact.module()).is_some())
            .unwrap()
            .1
            .module(),
        first,
        "the good family's local11 proof precedes the corrupted other graph's checked family"
    );
    assert_eq!(
        changed.authenticate_scalar_preflights(&mut TypeWorkBudget::default()),
        Err(ResolvedBuildFailure::InvalidState)
    );
    view.authenticate_scalar_preflights(&mut TypeWorkBudget::default())
        .unwrap();
}

#[test]
fn checked_memory_owned_projection_authenticates_before_publication_and_refuses_collisions() {
    let view = original_view();
    view.authenticate_scalar_preflights(&mut TypeWorkBudget::default())
        .unwrap();
    let empty = || {
        let mut candidate = view.clone();
        candidate.scalar_preflights.clear();
        candidate
    };
    let mut measured = TypeWorkBudget::default();
    let admitted = empty()
        .with_scalar_preflights(view.scalar_preflights(), &mut measured)
        .expect("the complete genuine projected table authenticates before publication");
    for (id, fact) in view.scalar_preflights() {
        assert!(Arc::ptr_eq(admitted.scalar_preflight(id).unwrap(), fact));
    }
    let cost = measured.used();
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        empty()
            .with_scalar_preflights(view.scalar_preflights(), &mut exact)
            .unwrap();
        assert_eq!(exact.used(), prefix + cost);
        assert!(matches!(
            empty().with_scalar_preflights(view.scalar_preflights(), &mut exact),
            Err(ResolvedBuildFailure::TypeResource)
        ));
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert!(matches!(
            empty().with_scalar_preflights(view.scalar_preflights(), &mut short),
            Err(ResolvedBuildFailure::TypeResource)
        ));
        let mut fresh = TypeWorkBudget::with_limit(cost);
        empty()
            .with_scalar_preflights(view.scalar_preflights(), &mut fresh)
            .unwrap();
        assert_eq!(fresh.used(), cost);
    }
    let (function, fact) = view
        .scalar_preflights()
        .find(|(id, _)| id.local() == 14)
        .unwrap();
    let repeated = [(function, fact), (function, fact)];
    let retained = admitted
        .with_scalar_preflights(repeated, &mut TypeWorkBudget::default())
        .unwrap();
    assert!(Arc::ptr_eq(
        retained.scalar_preflight(function).unwrap(),
        fact
    ));
    let duplicate = crate::foreign::scalar_preflight::CheckedForeignScalarPreflight::from_original(
        fact.role(),
        fact.source(),
        fact.origin(),
        fact.annotation(),
        Arc::clone(fact.call_codec()),
        &mut TypeWorkBudget::default(),
    )
    .unwrap();
    duplicate
        .authenticate(&view, &mut TypeWorkBudget::default())
        .unwrap();
    let duplicate = Arc::new(duplicate);
    assert!(matches!(
        view.clone()
            .with_scalar_preflights([(function, &duplicate)], &mut TypeWorkBudget::default()),
        Err(ResolvedBuildFailure::InvalidState)
    ));
    assert!(matches!(
        empty().with_scalar_preflights(
            [(BinderId::resolved(fact.module(), 999), fact)],
            &mut TypeWorkBudget::default()
        ),
        Err(ResolvedBuildFailure::InvalidState)
    ));
    for missing in [0, 11] {
        let partial = || {
            view.scalar_preflights()
                .filter(|(id, _)| id.local() != missing)
        };
        let mut standalone = empty();
        for (_, fact) in partial() {
            standalone
                .retain_scalar_preflight(Arc::clone(fact), &mut TypeWorkBudget::default())
                .expect("the existing standalone path permits selective non-anchor facts");
        }
        let projected = empty()
            .with_scalar_preflights(partial(), &mut TypeWorkBudget::default())
            .expect("pointwise projection does not invent an unselected family anchor");
        assert!(
            projected
                .scalar_preflight(BinderId::resolved(fact.module(), missing))
                .is_none()
        );
        assert_eq!(
            projected.scalar_preflights().count(),
            standalone.scalar_preflights().count()
        );
        assert_eq!(
            projected.authenticate_scalar_preflights(&mut TypeWorkBudget::default()),
            Err(ResolvedBuildFailure::InvalidState)
        );
    }
    let codec = crate::foreign::checked_source::CheckedForeignCallCodec::authenticate(
        fact.module(),
        fact.source(),
        fact.call_codec().ids(),
        &view,
        &mut TypeWorkBudget::default(),
    )
    .unwrap();
    let reminted = Arc::new(
        crate::foreign::scalar_preflight::CheckedForeignScalarPreflight::from_original(
            fact.role(),
            fact.source(),
            fact.origin(),
            fact.annotation(),
            Arc::new(codec),
            &mut TypeWorkBudget::default(),
        )
        .unwrap(),
    );
    reminted
        .authenticate(&view, &mut TypeWorkBudget::default())
        .unwrap();
    let mut codec_work = TypeWorkBudget::default();
    crate::foreign::checked_source::CheckedForeignCallCodec::authenticate(
        fact.module(),
        fact.source(),
        fact.call_codec().ids(),
        &view,
        &mut codec_work,
    )
    .unwrap();
    let mut distinct_work = TypeWorkBudget::default();
    let projected = empty()
        .with_scalar_preflights(
            view.scalar_preflights()
                .map(|(id, original)| (id, if id == function { &reminted } else { original })),
            &mut distinct_work,
        )
        .expect("a distinct independently valid codec gets its own pointwise proof");
    assert!(
        distinct_work.used() >= cost + codec_work.used(),
        "a second literal codec allocation must pay its own full proof"
    );
    assert_eq!(
        projected.authenticate_scalar_preflights(&mut TypeWorkBudget::default()),
        Err(ResolvedBuildFailure::InvalidState)
    );
    let mut malformed_target = empty();
    malformed_target
        .constructors
        .iter_mut()
        .find(|constructor| {
            constructor.id
                == crate::types::ConstructorId::new(
                    crate::types::NominalTypeId::new(fact.module(), 12),
                    2,
                )
        })
        .unwrap()
        .payload = Some(Type::Int);
    assert!(matches!(
        malformed_target
            .with_scalar_preflights(view.scalar_preflights(), &mut TypeWorkBudget::default()),
        Err(ResolvedBuildFailure::InvalidState)
    ));
    empty()
        .with_scalar_preflights(view.scalar_preflights(), &mut TypeWorkBudget::default())
        .unwrap();
    view.authenticate_scalar_preflights(&mut TypeWorkBudget::default())
        .unwrap();
}

fn selective_checked_summary() -> ExportSummary {
    let graph = graph("pub import @builtin.foreign (checked_copy_nul as selected)\n");
    let resolved = resolve_entry(&graph).unwrap();
    crate::elaborate::check_module(resolved)
        .unwrap()
        .into_exports()
}

fn authenticate_selective(
    summary: &ExportSummary,
    work: &mut TypeWorkBudget,
) -> Result<(), ResolvedBuildFailure> {
    summary.authenticate(
        work,
        &mut crate::interface::InterfaceConstraintBudget::default(),
    )
}

#[test]
fn checked_memory_selective_summary_keeps_private_codec_dependencies_and_limits() {
    let summary = selective_checked_summary();
    let mut measured = TypeWorkBudget::default();
    authenticate_selective(&summary, &mut measured).unwrap();
    assert_eq!(summary.term_order, ["selected"]);
    assert!(summary.nominal_order.is_empty());
    assert!(summary.constructor_order.is_empty());
    assert!(summary.effect_names.is_empty());
    let original = summary.terms["selected"].scalar_preflight.as_ref().unwrap();
    assert_eq!(original.function().local(), 14);
    for (id, coordinates, family) in original.codec_nominal_dependencies() {
        let fact = summary.nominal_fact(id).unwrap();
        assert_eq!(!fact.constructors.is_empty(), family);
        assert_eq!(fact.parameter_count, coordinates.formals().len());
        assert_eq!(fact.constructor_count, coordinates.constructors().len());
    }
    let cost = measured.used();
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        authenticate_selective(&summary, &mut exact).unwrap();
        assert_eq!(exact.used(), prefix + cost);
        assert_eq!(
            authenticate_selective(&summary, &mut exact),
            Err(ResolvedBuildFailure::TypeResource)
        );
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            authenticate_selective(&summary, &mut short),
            Err(ResolvedBuildFailure::TypeResource)
        );
        let mut fresh = TypeWorkBudget::with_limit(cost);
        authenticate_selective(&summary, &mut fresh).unwrap();
        assert_eq!(fresh.used(), cost);
    }
}

#[test]
fn checked_memory_selective_summary_rejects_erased_codec_dependencies() {
    let mut summary = selective_checked_summary();
    authenticate_selective(&summary, &mut TypeWorkBudget::default()).unwrap();
    let original = Arc::clone(summary.terms["selected"].scalar_preflight.as_ref().unwrap());
    let call = NominalTypeId::new(original.module(), 1);
    let nominal = summary.hidden_nominals.remove(&call).unwrap();
    let position = summary
        .hidden_nominal_order
        .iter()
        .position(|id| *id == call)
        .unwrap();
    summary.hidden_nominal_order.remove(position);
    assert_eq!(
        authenticate_selective(&summary, &mut TypeWorkBudget::default()),
        Err(ResolvedBuildFailure::InvalidState)
    );
    summary.hidden_nominals.insert(call, nominal);
    summary.hidden_nominal_order.insert(position, call);
    authenticate_selective(&summary, &mut TypeWorkBudget::default()).unwrap();

    // Remove the dense tail and lower both claimed counts. Present constructor
    // originals alone cannot certify that the entire canonical family remains.
    let tail = ConstructorId::new(call, 1);
    let constructor = summary.hidden_constructors.remove(&tail).unwrap();
    let position = summary
        .hidden_constructor_order
        .iter()
        .position(|id| *id == tail)
        .unwrap();
    summary.hidden_constructor_order.remove(position);
    let nominal = summary.hidden_nominals.get_mut(&call).unwrap();
    assert_eq!(nominal.constructor_count, 2);
    assert_eq!(
        nominal.constructors.as_ref(),
        &[ConstructorId::new(call, 0), tail]
    );
    nominal.constructors = vec![ConstructorId::new(call, 0)].into_boxed_slice();
    nominal.constructor_count = 1;
    assert_eq!(
        authenticate_selective(&summary, &mut TypeWorkBudget::default()),
        Err(ResolvedBuildFailure::InvalidState)
    );
    let nominal = summary.hidden_nominals.get_mut(&call).unwrap();
    nominal.constructor_count = 2;
    nominal.constructors = vec![ConstructorId::new(call, 0), tail].into_boxed_slice();
    summary.hidden_constructors.insert(tail, constructor);
    summary.hidden_constructor_order.insert(position, tail);
    authenticate_selective(&summary, &mut TypeWorkBudget::default()).unwrap();

    let host = original.codec_host_dependency().unwrap();
    let position = summary.effect_positions.remove(&host).unwrap();
    let effect = summary.effects.remove(position);
    for index in summary.effect_positions.values_mut() {
        if *index > position {
            *index -= 1;
        }
    }
    assert_eq!(
        authenticate_selective(&summary, &mut TypeWorkBudget::default()),
        Err(ResolvedBuildFailure::InvalidState)
    );
    summary.effects.insert(position, effect);
    for index in summary.effect_positions.values_mut() {
        if *index >= position {
            *index += 1;
        }
    }
    summary.effect_positions.insert(host, position);
    authenticate_selective(&summary, &mut TypeWorkBudget::default()).unwrap();
    assert!(Arc::ptr_eq(
        &original,
        summary.terms["selected"].scalar_preflight.as_ref().unwrap()
    ));
}

#[test]
fn scalar_owner_authentication_is_single_registry_bound_and_freshly_paid() {
    let view = original_view();
    let equal = view.clone();
    let independent = original_view();
    for registry in [&view, &equal, &independent] {
        registry
            .authenticate_owner_definitions(&mut TypeWorkBudget::default())
            .unwrap();
    }
    let mut measured = TypeWorkBudget::default();
    let authentication = view
        .authenticate_scalar_preflights_for_owners(&mut measured)
        .unwrap();
    let used = measured.used();
    view.authenticate_owner_definitions_with_preflights(
        authentication,
        &mut TypeWorkBudget::default(),
    )
    .unwrap();
    let combined = |work: &mut TypeWorkBudget| {
        let authentication = view.authenticate_scalar_preflights_for_owners(work)?;
        view.authenticate_owner_definitions_with_preflights(authentication, work)
            .map(drop)
    };
    let mut complete = TypeWorkBudget::default();
    combined(&mut complete).unwrap();
    let complete_cost = complete.used();
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + complete_cost);
        exact.charge(prefix).unwrap();
        combined(&mut exact).unwrap();
        assert_eq!(exact.used(), prefix + complete_cost);
        assert_eq!(
            combined(&mut exact),
            Err(ResolvedBuildFailure::TypeResource)
        );
        let mut short = TypeWorkBudget::with_limit(prefix + complete_cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            combined(&mut short),
            Err(ResolvedBuildFailure::TypeResource)
        );
    }
    for _ in 0..2 {
        let mut fresh = TypeWorkBudget::default();
        combined(&mut fresh).unwrap();
        assert_eq!(fresh.used(), complete_cost);
    }

    for other in [&equal, &independent] {
        let authentication = view
            .authenticate_scalar_preflights_for_owners(&mut TypeWorkBudget::default())
            .unwrap();
        assert_eq!(
            other
                .authenticate_owner_definitions_with_preflights(
                    authentication,
                    &mut TypeWorkBudget::default()
                )
                .map(drop),
            Err(ResolvedBuildFailure::InvalidState)
        );
    }
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + used);
        exact.charge(prefix).unwrap();
        let authentication = view
            .authenticate_scalar_preflights_for_owners(&mut exact)
            .unwrap();
        assert_eq!(exact.used(), prefix + used);
        view.authenticate_owner_definitions_with_preflights(
            authentication,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
    }
    for limit in [used - 1, 0] {
        assert!(matches!(
            view.authenticate_scalar_preflights_for_owners(&mut TypeWorkBudget::with_limit(limit)),
            Err(ResolvedBuildFailure::TypeResource)
        ));
    }
    let authentication = view
        .authenticate_scalar_preflights_for_owners(&mut TypeWorkBudget::default())
        .unwrap();
    assert_eq!(
        view.authenticate_owner_definitions_with_preflights(
            authentication,
            &mut TypeWorkBudget::with_limit(0)
        )
        .map(drop),
        Err(ResolvedBuildFailure::TypeResource)
    );
    for _ in 0..2 {
        let mut fresh = TypeWorkBudget::default();
        let authentication = view
            .authenticate_scalar_preflights_for_owners(&mut fresh)
            .unwrap();
        assert_eq!(fresh.used(), used);
        view.authenticate_owner_definitions_with_preflights(
            authentication,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
    }
}

#[test]
fn scalar_owner_host_chain_requires_exact_checked_family_and_fresh_host_projection() {
    let view = original_view();
    let module = view.scalar_preflights.values().next().unwrap().module();
    let host = view.effect(crate::types::EffectId::new(module, 0)).unwrap();
    let chain = |registry: &ResolvedRegistry, work: &mut TypeWorkBudget| {
        let scalar = registry.authenticate_scalar_preflights_for_owners(work)?;
        let host_proof = registry.authenticate_owner_definitions_with_preflights(scalar, work)?;
        assert!(
            host_proof
                .is_canonical_native_host(host, registry, work)
                .unwrap()
        );
        Ok::<(), ResolvedBuildFailure>(())
    };
    let mut full = TypeWorkBudget::default();
    assert!(
        crate::foreign::checked_builtins::is_canonical_native_host(host, &view, &mut full).unwrap()
    );
    let scalar = view
        .authenticate_scalar_preflights_for_owners(&mut TypeWorkBudget::default())
        .unwrap();
    let proof = view
        .authenticate_owner_definitions_with_preflights(scalar, &mut TypeWorkBudget::default())
        .unwrap();
    let mut projected = TypeWorkBudget::default();
    assert!(
        proof
            .is_canonical_native_host(host, &view, &mut projected)
            .unwrap()
    );
    assert!(projected.used() < full.used());
    let equal = view.clone();
    assert!(
        proof
            .is_canonical_native_host(host, &equal, &mut TypeWorkBudget::default())
            .is_err()
    );
    let mut wrong = host.clone();
    wrong.parameters[0].id = TypeVariableId::resolved(module, 23);
    assert!(
        !proof
            .is_canonical_native_host(&wrong, &view, &mut TypeWorkBudget::default())
            .unwrap()
    );
    assert!(
        proof
            .is_canonical_native_host(host, &view, &mut TypeWorkBudget::default())
            .unwrap()
    );
    let mut wrong_span = host.clone();
    wrong_span.span = host.origin.primary_span();
    assert!(
        !proof
            .is_canonical_native_host(&wrong_span, &view, &mut TypeWorkBudget::default())
            .unwrap()
    );
    let mut wrong_origin = host.clone();
    wrong_origin.parameters[0].origin = host.origin.clone();
    assert!(
        !proof
            .is_canonical_native_host(&wrong_origin, &view, &mut TypeWorkBudget::default())
            .unwrap()
    );
    let mut wrong_mirror = view.clone();
    wrong_mirror
        .type_variables
        .get_mut(&TypeVariableId::resolved(module, 22))
        .unwrap()
        .kind = Kind::EffectRow;
    assert!(matches!(
        wrong_mirror.authenticate_scalar_preflights_for_owners(&mut TypeWorkBudget::default()),
        Err(ResolvedBuildFailure::InvalidState)
    ));
    let mut measured = TypeWorkBudget::default();
    chain(&view, &mut measured).unwrap();
    let cost = measured.used();
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        chain(&view, &mut exact).unwrap();
        assert_eq!(exact.used(), prefix + cost);
        assert!(chain(&view, &mut exact).is_err());
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        // The final Host projection also uses the same cumulative meter.
        let scalar = view
            .authenticate_scalar_preflights_for_owners(&mut short)
            .unwrap();
        let proof = view
            .authenticate_owner_definitions_with_preflights(scalar, &mut short)
            .unwrap();
        assert!(
            proof
                .is_canonical_native_host(host, &view, &mut short)
                .unwrap_err()
                .is_resource_exhaustion()
        );
    }
    for _ in 0..2 {
        let mut fresh = TypeWorkBudget::default();
        chain(&view, &mut fresh).unwrap();
        assert_eq!(fresh.used(), cost);
    }
    for empty in [false, true] {
        let mut uncovered = view.clone();
        uncovered
            .scalar_preflights
            .retain(|_, fact| !empty && fact.role().host_parameter(fact.module()).is_none());
        let scalar = uncovered
            .authenticate_scalar_preflights_for_owners(&mut TypeWorkBudget::default())
            .unwrap();
        let proof = uncovered
            .authenticate_owner_definitions_with_preflights(scalar, &mut TypeWorkBudget::default())
            .unwrap();
        let declaration = uncovered.effect(host.id).unwrap();
        let mut fallback = TypeWorkBudget::default();
        assert!(
            proof
                .is_canonical_native_host(declaration, &uncovered, &mut fallback)
                .unwrap()
        );
        assert!(
            fallback.used() >= full.used(),
            "uncovered tables must pay the full inventory proof"
        );
    }
}

#[test]
fn scalar_owner_source_host_legacy_table_pays_full_checked_inventory_fallback() {
    let mut view = original_view();
    view.scalar_preflights
        .retain(|_, fact| fact.role().host_parameter(fact.module()).is_none());
    let module = view.scalar_preflights.values().next().unwrap().module();
    assert!(
        view.scalar_preflights
            .contains_key(&BinderId::resolved(module, 0))
    );
    assert!(
        view.scalar_preflights
            .values()
            .all(|fact| fact.call_codec().ids().call.declaration() == 1)
    );
    view.authenticate_scalar_preflights(&mut TypeWorkBudget::default())
        .unwrap();
    let scalar = view
        .authenticate_scalar_preflights_for_owners(&mut TypeWorkBudget::default())
        .unwrap();
    let host = view.effect(crate::types::EffectId::new(module, 0)).unwrap();
    let mut full = TypeWorkBudget::default();
    assert!(
        crate::foreign::checked_builtins::is_canonical_native_host(host, &view, &mut full).unwrap()
    );
    let mut fallback = TypeWorkBudget::default();
    assert!(
        crate::foreign::checked_builtins::is_canonical_native_host_with_preflights(
            host,
            &view,
            &scalar,
            &mut fallback
        )
        .unwrap()
    );
    assert!(fallback.used() >= full.used());
    view.constructors
        .iter_mut()
        .find(|constructor| constructor.id == ConstructorId::new(NominalTypeId::new(module, 12), 2))
        .unwrap()
        .payload = Some(Type::Int);
    // A genuine legacy family still authenticates, but cannot certify the
    // independently malformed checked-only BoundaryFailed role.
    view.authenticate_scalar_preflights(&mut TypeWorkBudget::default())
        .unwrap();
    let scalar = view
        .authenticate_scalar_preflights_for_owners(&mut TypeWorkBudget::default())
        .unwrap();
    let host = view.effect(crate::types::EffectId::new(module, 0)).unwrap();
    assert!(
        !crate::foreign::checked_builtins::is_canonical_native_host(
            host,
            &view,
            &mut TypeWorkBudget::default()
        )
        .unwrap()
    );
    assert!(
        !crate::foreign::checked_builtins::is_canonical_native_host_with_preflights(
            host,
            &view,
            &scalar,
            &mut TypeWorkBudget::default()
        )
        .unwrap()
    );
    let fresh = original_view();
    fresh
        .authenticate_scalar_preflights(&mut TypeWorkBudget::default())
        .unwrap();
}

#[test]
fn checked_memory_preflight_work_is_canonical_across_fresh_tables_and_insertion_orders() {
    use crate::foreign::checked_source::ForeignAdmissionReason;
    let mut expected = [None, None];
    // Independent genuine producer graphs, then fresh map seeds and different
    // insertion orders. Fact and codec allocation identities remain original.
    for _ in 0..2 {
        let original = original_view();
        original
            .authenticate_scalar_preflights(&mut TypeWorkBudget::default())
            .unwrap();
        let mut rows = original
            .scalar_preflights()
            .map(|(id, fact)| (id, Arc::clone(fact)))
            .collect::<Vec<_>>();
        rows.sort_by_key(|(id, _)| *id); // Test setup, outside measured admission.
        assert_eq!(rows.len(), 14);
        for order in 0..3 {
            let mut candidate = original.clone();
            candidate.scalar_preflights = HashMap::new();
            let count = rows.len();
            for index in 0..count {
                let selected = match order {
                    0 => index,
                    1 => count - index - 1,
                    _ => (index + 5) % count,
                };
                let (id, fact) = &rows[selected];
                candidate.scalar_preflights.insert(*id, Arc::clone(fact));
            }
            for (mode, pointwise) in [false, true].into_iter().enumerate() {
                let run = |work: &mut TypeWorkBudget| {
                    if pointwise {
                        crate::foreign::scalar_preflight::admit_projected_preflights(
                            candidate.clone(),
                            work,
                        )
                        .map(drop)
                    } else {
                        crate::foreign::scalar_preflight::authenticate_registry_families(
                            &candidate, work,
                        )
                    }
                };
                let mut measured = TypeWorkBudget::default();
                run(&mut measured).unwrap();
                let cost = measured.used();
                assert!(cost > 0);
                assert_eq!(*expected[mode].get_or_insert(cost), cost);
                for prefix in [0, 7] {
                    let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                    exact.charge(prefix).unwrap();
                    run(&mut exact).unwrap();
                    assert_eq!(exact.used(), prefix + cost);
                    assert_eq!(
                        run(&mut exact).unwrap_err().reason(),
                        ForeignAdmissionReason::WorkExhausted
                    );
                    let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                    short.charge(prefix).unwrap();
                    assert_eq!(
                        run(&mut short).unwrap_err().reason(),
                        ForeignAdmissionReason::WorkExhausted
                    );
                }
                for _ in 0..2 {
                    let mut fresh = TypeWorkBudget::with_limit(cost);
                    run(&mut fresh).unwrap();
                    assert_eq!(fresh.used(), cost);
                }
            }
        }
    }
}
