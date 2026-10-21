//! Real hidden source-resource provider interfaces, without native execution.

use super::*;
use crate::{
    module::{ModuleGraph, ModuleRoots},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason},
};
use std::sync::atomic::{AtomicU64, Ordering};

const SOURCE: &str = include_str!("../../tests/fixtures/checked-owner-lifecycle/owner.ash");

fn graph_for_source(source: &str, consumer: Option<&str>) -> ModuleGraph {
    static IDS: AtomicU64 = AtomicU64::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-hidden-checked-provider-{}-{}",
        std::process::id(),
        IDS.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    std::fs::write(directory.join("producer.ash"), source).unwrap();
    let entry = if let Some(consumer) = consumer {
        std::fs::write(directory.join("entry.ash"), consumer).unwrap();
        directory.join("entry.ash")
    } else {
        directory.join("producer.ash")
    };
    let graph = crate::module::load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    graph
}

fn graph(consumer: Option<&str>) -> ModuleGraph {
    graph_for_source(SOURCE, consumer)
}

fn check_graph(graph: &ModuleGraph) -> Result<Vec<CheckedModule>, ResolveModuleError> {
    let mut checked = Vec::<CheckedModule>::new();
    let mut availability = crate::elaborate::ProviderCodeAvailability::default();
    let (mut checking, bytes) = crate::compiler_work::source_work(graph).unwrap();
    let limit = checking.limit();
    checking
        .finish_sizing(crate::calibration::limit(
            limit,
            crate::calibration::DiagnosticOwner::Structural,
        ))
        .unwrap();
    let rewrite = crate::calibration::limit(
        crate::compiler_work::rewrite_total(bytes).unwrap(),
        crate::calibration::DiagnosticOwner::Structural,
    );
    let mut coverage = crate::pattern::UsefulnessBudget::default();
    let mut constraints = crate::interface::InterfaceConstraintBudget::default();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(
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
        let resolved = crate::resolve::resolve_checked_foreign_module(loaded, &dependencies)?;
        let module = crate::elaborate::check_module_with_budget_and_provider_codes_and_rewrite_work(resolved, &availability, &mut checking, &mut coverage, &mut constraints, Some(TypeWorkBudget::with_limit(rewrite)))
            .expect("real checked lifecycle source completes under normal source-phase funding before summary mutation");
        if let Some(code) = module.provider_code() {
            availability
                .retain(module.module(), code, &mut checking)
                .unwrap();
        }
        if let Some(code) = module.source_resource_code() {
            availability
                .retain_source(module.module(), code, &mut checking)
                .unwrap();
        }
        checked.push(module);
    }
    Ok(checked)
}

fn producer() -> CheckedModule {
    check_graph(&graph(None)).unwrap().pop().unwrap()
}

fn authenticate(
    summary: &ExportSummary,
    work: &mut TypeWorkBudget,
) -> Result<(), ResolvedBuildFailure> {
    summary.authenticate(
        work,
        &mut crate::interface::InterfaceConstraintBudget::default(),
    )
}

fn assert_hidden_provider(module: &CheckedModule) -> InterfaceId {
    let summary = module.exports();
    authenticate(summary, &mut TypeWorkBudget::default())
        .expect("canonical hidden-provider summary authenticates under the default allowance");
    let header = summary
        .source_resource_facts
        .values()
        .find(|fact| fact.id.module() == module.module() && fact.spelling == "Probe")
        .expect("real retained private resource header");
    let id = header.provider.interface.id;
    assert_eq!(id.module(), module.module());
    let mut facts = summary
        .hidden_interfaces
        .iter()
        .filter(|fact| fact.id == id);
    let hidden = facts
        .next()
        .expect("exact private provider interface is retained");
    assert!(facts.next().is_none());
    assert_eq!(hidden.spelling, "ProbeProvider");
    let checked = module
        .interface_facts()
        .iter()
        .find(|fact| fact.id == id)
        .unwrap();
    assert!(
        std::ptr::eq(hidden.as_ref(), checked.as_ref()),
        "publication forwards the immutable actual checked interface fact"
    );
    assert!(!summary.interface_names.contains_key("ProbeProvider"));
    assert!(
        !summary
            .interface_names
            .values()
            .any(|candidate| *candidate == id)
    );
    assert!(!summary.interface_positions.contains_key(&id));
    assert!(!summary.interfaces.iter().any(|fact| fact.id == id));
    for method in &hidden.methods {
        assert!(!summary.method_names.contains_key(&method.spelling));
        assert!(
            !summary
                .method_names
                .values()
                .any(|candidate| *candidate == method.id)
        );
    }
    id
}

#[test]
fn checked_hidden_provider_interface_is_retained_without_public_names() {
    assert_hidden_provider(&producer());
}

#[test]
fn checked_hidden_provider_interface_missing_exact_fact_refuses() {
    let module = producer();
    let required = assert_hidden_provider(&module);
    let mut summary = module.into_exports();
    let before = summary.hidden_interfaces.len();
    summary.hidden_interfaces.retain(|fact| fact.id != required);
    assert_eq!(summary.hidden_interfaces.len() + 1, before);
    assert_eq!(
        authenticate(&summary, &mut TypeWorkBudget::default()),
        Err(ResolvedBuildFailure::InvalidState)
    );
}

#[test]
fn checked_hidden_provider_interface_genuine_donor_cannot_replace_required_identity() {
    let module = producer();
    let required = assert_hidden_provider(&module);
    let donor = producer();
    let donor_id = assert_hidden_provider(&donor);
    assert_ne!(required.module(), donor_id.module());
    let donor_fact = donor
        .exports()
        .hidden_interfaces
        .iter()
        .find(|fact| fact.id == donor_id)
        .unwrap();
    let mut summary = module.into_exports();
    let slot = summary
        .hidden_interfaces
        .iter()
        .position(|fact| fact.id == required)
        .unwrap();
    let original = &summary.hidden_interfaces[slot];
    assert_eq!(original.spelling, donor_fact.spelling);
    assert_eq!(original.parameters.len(), donor_fact.parameters.len());
    assert_eq!(original.methods.len(), donor_fact.methods.len());
    // Forward a genuine immutable fact from another completed producer; never
    // rewrite its admitted ID or mint a same-shaped checked fact in the test.
    summary.hidden_interfaces[slot] = donor_fact.clone();
    assert_eq!(
        authenticate(&summary, &mut TypeWorkBudget::default()),
        Err(ResolvedBuildFailure::InvalidState)
    );
}

#[test]
fn checked_hidden_provider_interface_summary_has_exact_prefix_short_spent_fresh_limits() {
    let module = producer();
    assert_hidden_provider(&module);
    let summary = module.exports();
    let mut measured = TypeWorkBudget::default();
    authenticate(summary, &mut measured).unwrap();
    let cost = measured.used();
    assert!(cost > 0);
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        authenticate(summary, &mut exact).unwrap();
        assert_eq!(exact.used(), prefix + cost);
        assert_eq!(
            authenticate(summary, &mut exact),
            Err(ResolvedBuildFailure::TypeResource)
        );
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            authenticate(summary, &mut short),
            Err(ResolvedBuildFailure::TypeResource)
        );
    }
    for _ in 0..2 {
        let mut fresh = TypeWorkBudget::with_limit(cost);
        authenticate(summary, &mut fresh).unwrap();
        assert_eq!(fresh.used(), cost);
    }
}

#[test]
fn checked_hidden_provider_interface_cannot_be_imported_by_private_spelling() {
    assert_hidden_provider(&producer());
    let graph = graph(Some(
        "import producer (ProbeProvider)\nmain : Unit -> Int\nmain () = 42\n",
    ));
    let error = check_graph(&graph)
        .expect_err("hidden provider retention must not publish the private interface name");
    assert!(
        matches!(error, ResolveModuleError::Resolution(ref diagnostic) if diagnostic.reason == ResolveReason::UnavailableExport),
        "expected private export refusal after genuine producer checking: {error:?}"
    );
}

#[test]
fn checked_hidden_provider_interface_local_share_rejects_source_method_mirrors() {
    let module = producer();
    let id = assert_hidden_provider(&module);
    let fact = module
        .interface_facts()
        .iter()
        .find(|fact| fact.id == id)
        .unwrap();
    let source = module
        .interfaces()
        .iter()
        .find(|source| source.id == id)
        .unwrap();
    let share = |source: &ResolvedInterfaceDeclaration| {
        share_checked_interface_fact(
            fact,
            Some(source),
            &mut TypeWorkBudget::default(),
            &mut crate::interface::InterfaceConstraintBudget::default(),
        )
    };
    let canonical = share(source)
        .expect("genuine same-graph source and checked local provider fact share canonically");
    assert!(std::ptr::eq(canonical.as_ref(), fact.as_ref()));
    let mut wrong_annotation = source.clone();
    assert_ne!(wrong_annotation.methods[0].annotation.span, source.span);
    wrong_annotation.methods[0].annotation.span = source.span;
    assert_eq!(
        share(&wrong_annotation),
        Err(ResolvedBuildFailure::InvalidState)
    );
    let mut wrong_origin = source.clone();
    assert_ne!(wrong_origin.methods[0].origin.primary_span(), source.span);
    wrong_origin.methods[0].origin = Origin::Source(source.span);
    assert_eq!(
        share(&wrong_origin),
        Err(ResolvedBuildFailure::InvalidState)
    );
    let mut wrong_method_type = source.clone();
    assert_ne!(wrong_method_type.methods[0].annotation.ty, Type::Unit);
    wrong_method_type.methods[0].annotation.ty = Type::Unit;
    assert_eq!(
        share(&wrong_method_type),
        Err(ResolvedBuildFailure::InvalidState)
    );
    // Only cloned source claims changed; the admitted shared fact was never
    // detached, rewritten or reminted, and remains usable with its real source.
    let again = share(source).unwrap();
    assert!(std::ptr::eq(again.as_ref(), fact.as_ref()));
}

#[test]
fn checked_hidden_provider_interface_local_share_has_exact_constraint_limits() {
    let module = producer();
    let id = assert_hidden_provider(&module);
    let fact = module
        .interface_facts()
        .iter()
        .find(|fact| fact.id == id)
        .unwrap();
    let source = module
        .interfaces()
        .iter()
        .find(|source| source.id == id)
        .unwrap();
    let share = |constraints: &mut crate::interface::InterfaceConstraintBudget| {
        share_checked_interface_fact(
            fact,
            Some(source),
            &mut TypeWorkBudget::default(),
            constraints,
        )
    };
    let mut measured = crate::interface::InterfaceConstraintBudget::default();
    let canonical = share(&mut measured)
        .expect("canonical local source authentication before exact constraint controls");
    assert!(std::ptr::eq(canonical.as_ref(), fact.as_ref()));
    let cost = measured.used();
    assert!(cost > 0);
    for prefix in [0, 7] {
        let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        let retained = share(&mut exact).unwrap();
        assert!(std::ptr::eq(retained.as_ref(), fact.as_ref()));
        assert_eq!(exact.used(), prefix + cost);
        assert_eq!(
            share(&mut exact),
            Err(ResolvedBuildFailure::ConstraintResource)
        );
        let mut short = crate::interface::InterfaceConstraintBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            share(&mut short),
            Err(ResolvedBuildFailure::ConstraintResource)
        );
    }
    for _ in 0..2 {
        let mut fresh = crate::interface::InterfaceConstraintBudget::with_limit(cost);
        let retained = share(&mut fresh).unwrap();
        assert!(std::ptr::eq(retained.as_ref(), fact.as_ref()));
        assert_eq!(fresh.used(), cost);
    }
}

fn assert_hidden_state(module: &CheckedModule) -> NominalTypeId {
    assert_hidden_provider(module);
    let summary = module.exports();
    let header = summary
        .source_resource_facts
        .values()
        .find(|fact| fact.id.module() == module.module() && fact.spelling == "Probe")
        .unwrap();
    let state = header
        .state
        .ty
        .outer_nominal()
        .expect("actual original owner State application");
    let nominal = module
        .registry()
        .nominal(state)
        .expect("actual canonical passive owner nominal");
    assert_eq!(nominal.spelling, "State");
    let hidden = summary
        .hidden_nominals
        .get(&state)
        .expect("required private State has ordinary hidden metadata");
    assert_eq!(hidden.id, state);
    assert_eq!(hidden.spelling, "State");
    assert!(hidden.display_is_private);
    assert_eq!(hidden.access, ImportedTypeAccess::Hidden);
    assert_eq!(hidden.constructor_count, 0);
    assert!(hidden.constructors.is_empty());
    assert_eq!(
        hidden.parameters.as_ref(),
        module.registry().nominal_parameters(state).unwrap()
    );
    assert_eq!(hidden.parameter_count, 2);
    assert!(
        hidden
            .parameters
            .iter()
            .all(|parameter| parameter.kind == Kind::Type)
    );
    assert!(summary.hidden_nominal_order.contains(&state));
    assert!(!summary.nominal_names_by_id.contains_key(&state));
    assert!(!summary.nominals.values().any(|fact| fact.id == state));
    assert!(
        !summary
            .constructors
            .values()
            .any(|fact| fact.id.owner() == state)
    );
    assert!(
        !summary
            .hidden_constructors
            .keys()
            .any(|id| id.owner() == state)
    );
    state
}

#[test]
fn checked_hidden_private_state_retains_exact_owner_parameters_without_names() {
    assert_hidden_state(&producer());
}

#[test]
fn checked_hidden_private_state_missing_row_and_order_refuses() {
    let module = producer();
    let state = assert_hidden_state(&module);
    let mut summary = module.into_exports();
    let original_headers = summary
        .source_resource_facts
        .values()
        .cloned()
        .collect::<Vec<_>>();
    let original_native = summary.native_symbols.values().cloned().collect::<Vec<_>>();
    assert!(summary.hidden_nominals.remove(&state).is_some());
    summary.hidden_nominal_order.retain(|id| *id != state);
    assert!(original_headers.iter().all(|original| {
        summary
            .source_resource_facts
            .values()
            .any(|fact| Arc::ptr_eq(original, fact))
    }));
    assert!(original_native.iter().all(|original| {
        summary
            .native_symbols
            .values()
            .any(|fact| Arc::ptr_eq(original, fact))
    }));
    assert_eq!(
        authenticate(&summary, &mut TypeWorkBudget::default()),
        Err(ResolvedBuildFailure::InvalidState)
    );
}

#[test]
fn checked_hidden_private_state_same_kind_donor_parameters_refuse() {
    let module = producer();
    let state = assert_hidden_state(&module);
    let donor = producer();
    let donor_state = assert_hidden_state(&donor);
    assert_ne!(state.module(), donor_state.module());
    let donor_parameters = &donor.exports().hidden_nominals[&donor_state].parameters;
    let mut summary = module.into_exports();
    let hidden = summary.hidden_nominals.get_mut(&state).unwrap();
    assert_eq!(hidden.parameters.len(), donor_parameters.len());
    assert!(
        hidden
            .parameters
            .iter()
            .zip(donor_parameters.iter())
            .all(|(original, donor)| original.kind == donor.kind
                && original.spelling == donor.spelling
                && original.id != donor.id)
    );
    // Only the projected hidden parameter vector changes. The exact owner,
    // lifecycle, source header and native operation originals remain intact.
    hidden.parameters = donor_parameters.clone();
    assert_eq!(
        authenticate(&summary, &mut TypeWorkBudget::default()),
        Err(ResolvedBuildFailure::InvalidState)
    );
}

#[test]
fn checked_hidden_private_state_name_remains_unavailable_to_consumers() {
    assert_hidden_state(&producer());
    let graph = graph(Some(
        "import producer (State)\nmain : Unit -> Int\nmain () = 42\n",
    ));
    let error = check_graph(&graph)
        .expect_err("hidden State metadata cannot publish the private owner spelling");
    assert!(
        matches!(error, ResolveModuleError::Resolution(ref diagnostic) if diagnostic.reason == ResolveReason::UnavailableExport),
        "expected private State export refusal after genuine producer checking: {error:?}"
    );
}

#[test]
fn checked_hidden_private_state_does_not_retain_an_unreferenced_passive_owner() {
    assert_hidden_state(&producer());
    let prefix = SOURCE.split("\npub type Acquire").next().unwrap();
    let library = prefix
        .strip_prefix("import @builtin.foreign as Foreign\n")
        .unwrap()
        .replace("Memory", "UnusedMemory")
        .replace("Size", "UnusedSize")
        .replace("Address", "UnusedAddress")
        .replace("Callee", "UnusedCallee")
        .replace("State", "UnusedState")
        .replace("Allocate", "UnusedAllocate")
        .replace("Free", "UnusedFree");
    let source = format!(
        "import @builtin.foreign as Foreign\n{library}\npub idle : Unit -> Int\nidle () = 42\n"
    );
    let mut checked = check_graph(&graph_for_source(&source, None)).unwrap();
    let module = checked.pop().unwrap();
    let unused = module
        .registry()
        .nominals()
        .iter()
        .find(|nominal| nominal.id.module() == module.module() && nominal.spelling == "UnusedState")
        .expect("valid unrelated passive private owner was actually resolved");
    assert!(unused.constructors.is_empty());
    assert!(
        module
            .registry()
            .source_owner_candidates()
            .any(|(_, _, nominal, _)| nominal == unused.id)
    );
    let summary = module.exports();
    assert!(!summary.hidden_nominals.contains_key(&unused.id));
    assert!(!summary.hidden_nominal_order.contains(&unused.id));
    assert!(
        !summary
            .nominals
            .values()
            .any(|nominal| nominal.id == unused.id)
    );
    assert!(!summary.nominal_names_by_id.contains_key(&unused.id));
    authenticate(summary, &mut TypeWorkBudget::default()).unwrap();
}
