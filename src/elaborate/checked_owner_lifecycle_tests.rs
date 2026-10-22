//! Connected static checked lifecycle controls; no evaluator or native execution.

use super::*;
use crate::{
    module::{ModuleGraph, ModuleRoots},
    resolved::CheckedModule,
};
use std::sync::{
    Arc,
    atomic::{AtomicU64, Ordering},
};

const PRODUCER: &str = include_str!("../../tests/fixtures/checked-owner-lifecycle/owner.ash");

fn graph(producer: &str, consumer: bool) -> ModuleGraph {
    graph_with_entry(producer, consumer.then_some("import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Int, Unit, Unit>\nmain () = Producer.run ()\n"))
}

fn graph_with_entry(producer: &str, consumer: Option<&str>) -> ModuleGraph {
    static IDS: AtomicU64 = AtomicU64::new(0);
    struct OwnedFixtureDirectory(std::path::PathBuf);
    impl Drop for OwnedFixtureDirectory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let directory = loop {
        let candidate = std::env::temp_dir().join(format!(
            "ash-checked-owner-lifecycle-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        match std::fs::create_dir(&candidate) {
            Ok(()) => break OwnedFixtureDirectory(candidate),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("create owned lifecycle fixture: {error}"),
        }
    };
    let directory = &directory.0;
    std::fs::write(directory.join("producer.ash"), producer).unwrap();
    let entry = if let Some(consumer) = consumer {
        std::fs::write(directory.join("entry.ash"), consumer).unwrap();
        directory.join("entry.ash")
    } else {
        directory.join("producer.ash")
    };
    crate::module::load_module_graph(&entry, &ModuleRoots::empty()).unwrap()
}

fn check_graph(graph: &ModuleGraph) -> Result<Vec<CheckedModule>, TypeError> {
    let mut checked = Vec::<CheckedModule>::new();
    let mut availability = ProviderCodeAvailability::default();
    // This is the established modular source-phase funding, separate from the
    // unchanged standalone Core/image allowance. Resolution retains its own API.
    let (mut checking, source_bytes) = crate::compiler_work::source_work(graph).unwrap();
    let source_limit = checking.limit();
    checking
        .finish_sizing(crate::calibration::limit(
            source_limit,
            crate::calibration::DiagnosticOwner::Structural,
        ))
        .unwrap();
    let rewrite_limit = crate::calibration::limit(
        crate::compiler_work::rewrite_total(source_bytes).unwrap(),
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
        let resolved = crate::resolve::resolve_checked_foreign_module(loaded, &dependencies)
            .expect("canonical checked lifecycle source resolves before source checking");
        let module = check_module_with_budget_and_provider_codes_and_rewrite_work(
            resolved,
            &availability,
            &mut checking,
            &mut coverage,
            &mut constraints,
            Some(TypeWorkBudget::with_limit(rewrite_limit)),
        )?;
        module.exports().authenticate(&mut TypeWorkBudget::default(), &mut crate::interface::InterfaceConstraintBudget::default())
            .expect("completed body-free checked lifecycle summary authenticates under the default allowance");
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

fn assert_producer_originals(checked: &[CheckedModule]) {
    let producer = checked
        .iter()
        .find(|module| {
            module
                .registry()
                .source_resource_facts()
                .any(|fact| fact.id.module() == module.module() && fact.spelling == "Probe")
        })
        .expect("actual checked producer retains Probe metadata");
    let header = producer
        .registry()
        .source_resource_facts()
        .find(|fact| fact.id.module() == producer.module() && fact.spelling == "Probe")
        .unwrap();
    assert_eq!(header.host.unwrap().position, 0);
    assert_eq!(header.parameters[0].spelling, "H");
    assert_eq!(header.owned_position, 1);
    assert_eq!(header.parameters[1].spelling, "R");
    assert_ne!(header.parameters[0].id, header.parameters[1].id);
    assert_eq!(
        header.codec.kind,
        crate::surface::SurfaceResourceReportCodecKind::CheckedScope
    );
    let code = producer
        .source_resource_code()
        .expect("checked original lifecycle code");
    assert!(
        code.headers()
            .any(|actual| Arc::ptr_eq(&actual.original, header))
    );
    assert!(
        producer
            .exports()
            .source_resource_facts()
            .any(|actual| Arc::ptr_eq(actual, header)),
        "the body-free publication retains the exact required hidden header"
    );
    for name in ["Allocate", "Free"] {
        let effect = producer
            .registry()
            .effects()
            .iter()
            .find(|effect| effect.id.module() == producer.module() && effect.spelling == name)
            .unwrap();
        let original = producer
            .registry()
            .native_symbol(crate::types::OperationId::new(effect.id, 0))
            .unwrap();
        assert!(original.owner().is_some());
        let contract = original.prepared().checked_contract().unwrap();
        let selected = &contract.symbols()[original.symbol_index()];
        assert_eq!(selected.host_parameter(), 0);
        let callee = contract
            .assumptions()
            .iter()
            .find(|assumption| assumption.name() == "Callee")
            .unwrap();
        assert_eq!(
            callee.description(),
            "the admitted native owner contract holds"
        );
        assert!(
            selected
                .assumption_members()
                .contains(&callee.member_index())
        );
    }
}

#[test]
fn checked_owner_lifecycle_canonical_source_retains_originals() {
    let graph = graph(PRODUCER, false);
    let checked = check_graph(&graph).expect(
        "canonical checked lifecycle source must pass before any negative control receives credit",
    );
    assert_producer_originals(&checked);
}

#[test]
fn checked_owner_lifecycle_body_free_consumer_links_core_and_transforms() {
    let graph = graph(PRODUCER, true);
    let checked = check_graph(&graph)
        .expect("real body-free consumer checks the canonical checked lifecycle publication");
    assert_producer_originals(&checked);
    let producer = checked
        .iter()
        .find(|module| module.source_resource_code().is_some())
        .unwrap();
    let producer_id = producer.module();
    let original_code = Arc::clone(producer.source_resource_code().unwrap());
    let original_header = Arc::clone(original_code.headers().next().unwrap());
    let originals = [
        Arc::clone(&original_header.acquire),
        Arc::clone(&original_header.teardown),
    ];
    for original in &originals {
        assert!(Arc::ptr_eq(
            original_code
                .resource(0)
                .unwrap()
                .original_registry()
                .native_symbol(original.operation())
                .unwrap(),
            original,
        ));
    }
    let linked =
        link_modules(checked, graph.entry()).expect("canonical lifecycle module closure links");
    for original in &originals {
        assert!(Arc::ptr_eq(
            linked
                .registry()
                .native_symbol(original.operation())
                .unwrap(),
            original
        ));
    }
    assert!(Arc::ptr_eq(
        linked
            .registry()
            .source_resource_fact(original_header.original.id)
            .unwrap(),
        &original_header.original
    ));
    let producer_group = linked
        .groups()
        .iter()
        .find(|group| group.module() == producer_id)
        .unwrap();
    assert!(Arc::ptr_eq(
        producer_group.source_resource_code().unwrap(),
        &original_code
    ));
    let linked = crate::evidence_validation::validate_interface_evidence(linked)
        .expect("canonical lifecycle evidence authenticates");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("default final elaboration allowance");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("canonical checked lifecycle lowers to Effect Core under the default allowance");
    let program = elaborator.finish(typed.node).unwrap();
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let core = crate::core::validate_effect_modules(program, &sources, &modules)
        .expect("independent canonical checked lifecycle Core under the default allowance");
    {
        use crate::core::source_resource::checked_lifecycle_core_tests::{
            Mutation, assert_budget_controls, mutate_and_authenticate,
        };
        let canonical = crate::core::transform::identity_effect_traversal(&core).unwrap();
        assert_budget_controls(&canonical);
        for mutation in [
            Mutation::HostActual,
            Mutation::InterpretationActual,
            Mutation::FinishContinuation,
        ] {
            let mut candidate = crate::core::transform::identity_effect_traversal(&core).unwrap();
            mutate_and_authenticate(&mut candidate, mutation);
            let error = crate::core::validate_effect_modules(candidate, &sources, &modules)
                .expect_err("independent whole Core rejects the hostile copied scope");
            assert_ne!(
                error.reason(),
                crate::core::ValidationReason::Resource,
                "hostile scope must fail semantically rather than exhaust work: {error:?}"
            );
        }
    }
    {
        let mut candidate = crate::core::transform::identity_effect_traversal(&core).unwrap();
        crate::core::source_resource::checked_lifecycle_core_tests::erase_copied_completion_host_row(&mut candidate);
        let error = crate::core::validate_effect_modules(candidate, &sources, &modules).expect_err(
            "whole Core must reject erasing exact completion Host<H> from the copied scope row",
        );
        assert_ne!(error.reason(), crate::core::ValidationReason::Resource);
    }
    for transformed in [
        crate::core::transform::identity_effect_traversal(&core).unwrap(),
        crate::core::transform::fold_effect_literal_primitives(&core).unwrap(),
    ] {
        crate::core::validate_effect_modules(transformed, &sources, &modules).expect(
            "transformed checked lifecycle independently revalidates under the default allowance",
        );
    }
}

fn source_refusal_after_canonical(replacement: &str) {
    check_graph(&graph(PRODUCER, false))
        .expect("canonical source must pass before mutation rejection is meaningful");
    let arm = "Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason";
    assert_eq!(PRODUCER.matches(arm).count(), 1);
    let changed = PRODUCER.replace(arm, replacement);
    let error =
        check_graph(&graph(&changed, false)).expect_err("changed checked finish must be rejected");
    assert!(
        matches!(error, TypeError::Source(_)),
        "expected semantic source refusal, not resource exhaustion or an internal failure: {error:?}"
    );
}

#[test]
fn checked_owner_lifecycle_boundary_failure_cannot_claim_retention() {
    source_refusal_after_canonical(
        "Foreign.BoundaryFailed(reason) => Foreign.FinishedRetained(state, ())",
    );
}

#[test]
fn checked_owner_lifecycle_boundary_failure_retires_ordinary_state_access() {
    source_refusal_after_canonical(
        "Foreign.BoundaryFailed(reason) => {\n                let ignored : Unit = Foreign.data_of state\n                Foreign.FinishedBoundary reason\n            }",
    );
}

#[test]
fn checked_owner_lifecycle_default_profile_refuses_the_same_source() {
    let graph = graph(PRODUCER, false);
    let mut checked = Vec::<CheckedModule>::new();
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
        match crate::resolve::resolve_module(loaded, &dependencies) {
            Ok(resolved) => checked.push(check_module(resolved).unwrap()),
            Err(_) => {
                assert_eq!(loaded.id(), graph.entry());
                return;
            }
        }
    }
    panic!("default profile must refuse checked lifecycle source");
}

fn retained_void_teardown_source() -> String {
    let consumed = "outcome otherwise { consumed 0 }";
    assert_eq!(PRODUCER.matches(consumed).count(), 1);
    PRODUCER.replace(consumed, "outcome otherwise { retained 0 }")
}

fn assert_retained_void_teardown_source(source: &str) {
    let checked = check_graph(&graph(source, false))
        .expect("genuine retained void teardown source must pass before retained-outcome controls");
    assert_producer_originals(&checked);
    let producer = checked
        .iter()
        .find(|module| module.source_resource_code().is_some())
        .unwrap();
    let free = producer
        .registry()
        .effects()
        .iter()
        .find(|effect| effect.id.module() == producer.module() && effect.spelling == "Free")
        .unwrap();
    let original = producer
        .registry()
        .native_symbol(crate::types::OperationId::new(free.id, 0))
        .unwrap();
    assert!(
        matches!(
            original.owner_role(),
            Some(
                crate::foreign::source_contract::PreparedOwnerCall::Teardown {
                    consumes: false,
                    ..
                }
            )
        ),
        "the actual prepared teardown outcome must be retained, not a source-only result relabel"
    );
}

fn source_refusal_after_retained_canonical(arm: &str, replacement: &str) {
    let canonical = retained_void_teardown_source();
    assert_retained_void_teardown_source(&canonical);
    assert_eq!(canonical.matches(arm).count(), 1);
    let changed = canonical.replace(arm, replacement);
    let error = check_graph(&graph(&changed, false))
        .expect_err("changed retained teardown finish must be rejected");
    assert!(
        matches!(error, TypeError::Source(_)),
        "expected semantic source refusal after canonical retained source, not setup/resource failure: {error:?}"
    );
}

#[test]
fn checked_owner_lifecycle_boundary_failure_cannot_claim_consumption() {
    source_refusal_after_canonical(
        "Foreign.BoundaryFailed(reason) => Foreign.FinishedConsumed Foreign.FinishOk",
    );
}

#[test]
fn checked_owner_lifecycle_retained_void_teardown_has_a_genuine_canonical_source() {
    assert_retained_void_teardown_source(&retained_void_teardown_source());
}

#[test]
fn checked_owner_lifecycle_retained_native_outcome_cannot_claim_consumption() {
    source_refusal_after_retained_canonical(
        "Foreign.CheckedReturned(Foreign.Retained(())) => Foreign.FinishedRetained(state, ())",
        "Foreign.CheckedReturned(Foreign.Retained(())) => Foreign.FinishedConsumed Foreign.FinishOk",
    );
}

#[test]
fn checked_owner_lifecycle_boundary_failure_cannot_borrow_retained_native_outcome() {
    source_refusal_after_retained_canonical(
        "Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason",
        "Foreign.BoundaryFailed(reason) => Foreign.FinishedRetained(state, ())",
    );
}

#[test]
fn checked_owner_lifecycle_constructed_boundary_record_cannot_replace_request_witness() {
    source_refusal_after_canonical(
        "Foreign.BoundaryFailed(reason) => {\n                let forged = Foreign.SessionLost (Foreign.BoundaryRecord(Foreign.NoNativeStatus, Foreign.NativeUnknown, false, Foreign.DiagnosticUnavailable Foreign.NotRequested))\n                Foreign.FinishedBoundary forged\n            }",
    );
}

fn validate_latest_payload_core(graph: &ModuleGraph) {
    let checked = check_graph(graph).expect("canonical latest-payload source modules check");
    let linked = link_modules(checked, graph.entry()).expect("actual latest-payload closure links");
    let linked = crate::evidence_validation::validate_interface_evidence(linked)
        .expect("actual latest-payload evidence validates");
    let mut elaborator = EffectElaborator::for_module_program(&linked)
        .expect("latest-payload final elaboration uses default funding");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("latest-payload closure lowers without native execution");
    let program = elaborator.finish(typed.node).unwrap();
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let core = crate::core::validate_effect_modules(program, &sources, &modules)
        .expect("independent latest-payload Core uses unchanged default funding");
    for transformed in [
        crate::core::transform::identity_effect_traversal(&core).unwrap(),
        crate::core::transform::fold_effect_literal_primitives(&core).unwrap(),
    ] {
        crate::core::validate_effect_modules(transformed, &sources, &modules)
            .expect("latest-payload transformed Core independently revalidates");
    }
}

#[test]
fn checked_owner_lifecycle_latest_completion_e_retains_only_the_outer_owner() {
    let producer =
        include_str!("../../tests/fixtures/checked-owner-lifecycle/latest_payload_producer.ash");
    let within =
        include_str!("../../tests/fixtures/checked-owner-lifecycle/latest_payload_within.ash");
    let escape =
        include_str!("../../tests/fixtures/checked-owner-lifecycle/latest_payload_escape.ash");
    for retained in [false, true] {
        let producer = if retained {
            assert_eq!(
                producer.matches("outcome otherwise { consumed 0 }").count(),
                1
            );
            producer.replace(
                "outcome otherwise { consumed 0 }",
                "outcome otherwise { retained 0 }",
            )
        } else {
            producer.to_owned()
        };
        let within_graph = graph_with_entry(&producer, Some(within));
        check_graph(&within_graph).expect(
            "replacement E is usable while its distinct outer ordinary owner C remains live",
        );
        validate_latest_payload_core(&within_graph);
        assert_eq!(escape.matches("let retained = outer").count(), 1);
        let independent = escape.replace("let retained = outer", "let retained = 1");
        let independent_graph = graph_with_entry(&producer, Some(&independent));
        check_graph(&independent_graph)
            .expect("an independent latest callback permits the report to leave C");
        validate_latest_payload_core(&independent_graph);
        let error = check_graph(&graph_with_entry(&producer, Some(escape)))
            .expect_err("the latest callback must not escape C through CheckedCompletion E");
        assert!(
            matches!(error, TypeError::Source(ref diagnostic) if diagnostic.reason == TypeReason::ResourceEscape),
            "expected actual outer-owner capture refusal after both source positives: {error:?}"
        );
    }
}

#[test]
fn checked_owner_lifecycle_boundary_data_can_be_inspected_while_forwarding_original() {
    check_graph(&graph(PRODUCER, false)).unwrap();
    let arm = "Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason";
    let changed = PRODUCER.replace(arm, "Foreign.BoundaryFailed(reason) => {\n                let ignored = match reason {\n                    Foreign.SessionLost(_) => ()\n                    Foreign.DependencyBlocked(_) => ()\n                    Foreign.Quarantined(_) => ()\n                }\n                Foreign.FinishedBoundary reason\n            }");
    check_graph(&graph(&changed, false)).expect("independent boundary data can be inspected while forwarding the original whole witnessed reason");
}

#[test]
fn checked_owner_lifecycle_required_trace_survives_resource_and_host_boundaries() {
    let source = PRODUCER.replace(
        "pub run : Unit -> Foreign.CheckedScope<Int, Unit, Unit>\nrun () = handle (foreign host H {",
        "pub run : Unit -> Foreign.CheckedScope<Int, Unit, Unit> ! {Trace}\nrun () = foreign host H {",
    ).replace("}) with Trace {\n    note ignored => resume ()\n}", "}");
    assert_ne!(source, PRODUCER);
    let checked = check_graph(&graph(&source, false))
        .expect("required source Trace remains an outward effect after resource/host subtraction");
    let producer = checked
        .iter()
        .find(|module| module.source_resource_code().is_some())
        .unwrap();
    let trace = producer
        .effects()
        .iter()
        .find(|effect| effect.spelling == "Trace")
        .unwrap()
        .id;
    let template = producer
        .source_resource_code()
        .unwrap()
        .resource(0)
        .unwrap();
    let row = template
        .lifecycle_row(false, &mut TypeWorkBudget::default())
        .unwrap();
    assert!(
        row.known()
            .iter()
            .any(|instance| instance.effect() == trace)
    );
    assert!(
        row.known()
            .iter()
            .any(|instance| instance.effect().declaration()
                == crate::module::FOREIGN_NATIVE_HOST_LOCAL
                && instance.effect().module().is_builtin_foreign())
    );
    let run = producer
        .schemes()
        .iter()
        .find(|global| global.spelling == "run")
        .unwrap();
    let outward = run
        .scheme
        .value_type
        .function_view()
        .unwrap()
        .effects()
        .unwrap();
    assert_eq!(outward.known().len(), 1);
    assert_eq!(outward.known()[0].effect(), trace);
}

#[test]
fn checked_owner_lifecycle_required_postrequest_source_continuation_cannot_be_discarded() {
    check_graph(&graph(PRODUCER, false)).unwrap();
    let source = PRODUCER.replace(
        "note ignored => resume ()",
        "note ignored => {
    let done = discard
    Foreign.CheckedNotAcquired ()
}",
    );
    let error = check_graph(&graph(&source, false))
        .expect_err("required post-finish source continuation cannot be abandoned");
    assert!(
        matches!(error, TypeError::Source(ref diagnostic) if diagnostic.reason == TypeReason::DiscardUnsafe),
        "exact unsafe-discard refusal required: {error:?}"
    );
}

#[test]
fn checked_owner_lifecycle_inspected_boundary_fields_cannot_reconstruct_witness() {
    source_refusal_after_canonical(
        "Foreign.BoundaryFailed(reason) => match reason {\n                Foreign.SessionLost(record) => Foreign.FinishedBoundary (Foreign.SessionLost record)\n                Foreign.DependencyBlocked(record) => Foreign.FinishedBoundary (Foreign.DependencyBlocked record)\n                Foreign.Quarantined(record) => Foreign.FinishedBoundary (Foreign.Quarantined record)\n            }",
    );
}

// Connected source controls. Canonical parsing, resolution, checking and
// publication must succeed first; a setup panic never counts as a refusal.
fn connected_lifecycle_source_refusal(change: impl FnOnce(&str) -> String) {
    let checked = check_graph(&graph(PRODUCER, false))
        .expect("unchanged connected lifecycle source checks before every mutation");
    assert_producer_originals(&checked);
    let changed = change(PRODUCER);
    assert_ne!(changed, PRODUCER, "the intended source mutation must occur");
    let error = check_graph(&graph(&changed, false))
        .expect_err("mutated connected lifecycle source must be rejected");
    assert!(
        matches!(error, TypeError::Source(_)),
        "require a semantic source refusal after genuine parse/resolve, not setup, contract, resource or internal refusal: {error:?}"
    );
}

fn lifecycle_replace_once(source: &str, from: &str, to: &str) -> String {
    assert_eq!(source.matches(from).count(), 1, "exact mutation anchor");
    source.replacen(from, to, 1)
}

fn lifecycle_replace_finish(source: &str, body: impl FnOnce(&str) -> String) -> String {
    let start_marker = "    finish (state, data) => {\n";
    let end_marker = "    }\n    handlers (state, data) {";
    assert_eq!(source.matches(start_marker).count(), 1);
    assert_eq!(source.matches(end_marker).count(), 1);
    let start = source.find(start_marker).unwrap() + start_marker.len();
    let end = source[start..].find(end_marker).unwrap() + start;
    format!(
        "{}{}{}",
        &source[..start],
        body(&source[start..end]),
        &source[end..]
    )
}

#[test]
fn checked_owner_lifecycle_connected_finish_requires_a_free_attempt() {
    connected_lifecycle_source_refusal(|source| {
        lifecycle_replace_finish(source, |_| {
            "        let ignored = perform Trace.note ()\n        Foreign.FinishedConsumed Foreign.FinishOk\n".to_owned()
        })
    });
}

#[test]
fn checked_owner_lifecycle_connected_finish_rejects_duplicate_free_attempts() {
    connected_lifecycle_source_refusal(|source| {
        lifecycle_replace_once(
            source,
            "        let outcome = perform Free<H, R>.call state\n",
            "        let outcome = perform Free<H, R>.call state\n        let duplicate = perform Free<H, R>.call state\n",
        )
    });
}

#[test]
fn checked_owner_lifecycle_connected_every_returning_branch_requires_attempt() {
    connected_lifecycle_source_refusal(|source| {
        let attempted = |original: &str| {
            original
                .lines()
                .map(|line| format!("        {line}\n"))
                .collect::<String>()
        };
        let both = lifecycle_replace_finish(source, |original| {
            let attempted = attempted(original);
            format!(
                "        match true {{\n            true => {{\n{attempted}            }}\n            false => {{\n{attempted}            }}\n        }}\n"
            )
        });
        check_graph(&graph(&both, false))
            .expect("supported Bool branches with one genuine attempt each must check first");
        lifecycle_replace_finish(source, |original| {
            let attempted = attempted(original);
            format!(
                "        match true {{\n            true => {{\n                let ignored = perform Trace.note ()\n                Foreign.FinishedConsumed Foreign.FinishOk\n            }}\n            false => {{\n{attempted}            }}\n        }}\n"
            )
        })
    });
}

#[test]
fn checked_owner_lifecycle_connected_free_requires_exact_host_actual() {
    connected_lifecycle_source_refusal(|source| {
        lifecycle_replace_once(
            source,
            "perform Free<H, R>.call state",
            "perform Free<Int, R>.call state",
        )
    });
}

#[test]
fn checked_owner_lifecycle_connected_acquisition_requires_exact_host_actual() {
    connected_lifecycle_source_refusal(|source| {
        lifecycle_replace_once(
            source,
            "perform Allocate<H, R>.call size",
            "perform Allocate<Int, R>.call size",
        )
    });
}

#[test]
fn checked_owner_lifecycle_connected_coherent_state_vector_swap_is_not_authority() {
    connected_lifecycle_source_refusal(|source| {
        // Change every resource-local State and native vector coherently, leaving
        // the authored resource H/R selectors and foreign originals unchanged.
        let (library, resource) = source.split_once("resource Probe<H, R> {").unwrap();
        let resource = resource
            .replace("State<H, R>", "State<R, H>")
            .replace("Allocate<H, R>", "Allocate<R, H>")
            .replace("Free<H, R>", "Free<R, H>");
        format!("{library}resource Probe<H, R> {{{resource}")
    });
}

#[test]
fn checked_owner_lifecycle_connected_same_shape_finish_is_not_canonical_codec() {
    connected_lifecycle_source_refusal(|source| {
        let changed = lifecycle_replace_once(
            source,
            "pub type Acquire<S, D, I>",
            "type FakeFinish<S, E> = FakeConsumed(Foreign.FinishResult<E>)\n    | FakeRetained(S, E)\n    | FakeBoundary(Foreign.BoundaryFailure)\n\npub type Acquire<S, D, I>",
        );
        changed
            .replace(
                "Foreign.CheckedFinish<State<H, R>, Unit>",
                "FakeFinish<State<H, R>, Unit>",
            )
            .replace("Foreign.FinishedConsumed", "FakeConsumed")
            .replace("Foreign.FinishedRetained", "FakeRetained")
            .replace("Foreign.FinishedBoundary", "FakeBoundary")
    });
}

#[test]
fn checked_owner_lifecycle_connected_same_shape_scope_is_not_canonical_codec() {
    connected_lifecycle_source_refusal(|source| {
        let changed = lifecycle_replace_once(
            source,
            "pub type Acquire<S, D, I>",
            "pub type FakeScope<A, I, E> = FakeNotAcquired(I)\n    | FakeCompleted(A, Foreign.CheckedCompletion<E>)\n\npub type Acquire<S, D, I>",
        );
        changed.replace("Foreign.CheckedScope<", "FakeScope<")
    });
}

// Intended for the existing elaborate::checked_owner_lifecycle_tests child.
// DIRECT ROW/DEFERRED-ESCAPE HARNESS, not a finish_foreign_host/full-pipeline test.
// The canonical source and genuine prepared original instances are prerequisites;
// scheduling the late row is an explicit test injection, not observed source timing.
#[test]
fn checked_owner_lifecycle_host_pending_rows_do_not_hide_unknown_or_late_native() {
    let checked = check_graph(&graph(PRODUCER, false))
        .expect("actual canonical lifecycle source before direct pending-row controls");
    assert_producer_originals(&checked);
    let producer = checked
        .iter()
        .find(|module| module.source_resource_code().is_some())
        .unwrap();
    let registry = producer.registry();
    let header = registry
        .source_resource_facts()
        .find(|fact| fact.id.module() == producer.module() && fact.spelling == "Probe")
        .unwrap();
    let host_id = header.parameters[header.host.unwrap().position].id;
    let builtin = checked
        .iter()
        .find(|module| module.module().is_builtin_foreign())
        .expect("actual checked canonical builtin module");
    let native_host = builtin
        .registry()
        .effect(crate::types::EffectId::new(
            builtin.module(),
            crate::module::FOREIGN_NATIVE_HOST_LOCAL,
        ))
        .expect("actual retained builtin registry Host declaration");
    let host = crate::core::effect::ForeignHostIdentity {
        identity: host_id,
        effect: native_host.id,
    };
    let source = crate::source::SourceFile::new("pending-host-row-control.ash", "()").unwrap();
    let span = source
        .span(crate::source::ByteRange::new(0, 2).unwrap())
        .unwrap();
    let instance = |name: &str| {
        let effect = registry
            .effects()
            .iter()
            .find(|effect| effect.id.module() == producer.module() && effect.spelling == name)
            .unwrap();
        crate::types::EffectInstance::new_kinded(
            effect.id,
            header
                .parameters
                .iter()
                .map(|formal| crate::types::KindedArgument::TypeArg(Type::Variable(formal.id)))
                .collect(),
        )
    };
    // The hostile late native vector comes from the completed real header.
    // Its original checked contract selects exact H; no native fact is minted.
    let late = instance("Free");
    let instance = &late;
    let original = registry
        .native_symbol(crate::types::OperationId::new(instance.effect(), 0))
        .unwrap();
    let selected = crate::foreign::checked_source::checked_host_instance(
        original,
        instance,
        &mut TypeWorkBudget::default(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(selected.effect(), host.effect());
    assert!(
        matches!(selected.arguments(), [crate::types::KindedArgument::TypeArg(Type::Variable(id))] if *id == host_id)
    );
    let host_instance = || {
        crate::types::EffectInstance::new_kinded(
            host.effect(),
            Box::new([crate::types::KindedArgument::TypeArg(Type::Variable(
                host_id,
            ))]),
        )
    };

    // Fresh ordinary inference and a rigid row are NOT cleanup/provider-owned.
    // Neither may use the new pending-only path to assume absent effects.
    for rigid in [false, true] {
        let mut elaborator = EffectElaborator::new();
        let row = if rigid {
            let id = elaborator
                .fresh_type_variable(&Kind::EffectRow, span)
                .unwrap();
            EffectRow::open(crate::types::EffectRowVariable::rigid(id), Box::new([]))
        } else {
            elaborator.fresh_effect_row(span).unwrap()
        };
        assert!(!elaborator.cleanup_row_pending(&row));
        let error = crate::core::effect::foreign_host_outward_row(
            &row,
            &[],
            Some(host),
            &mut TypeWorkBudget::default(),
        )
        .expect_err("arbitrary unknown row is not eligible pending state");
        assert!(matches!(error, crate::core::BuildError::InvalidPayload));
    }

    for leave_unlisted_native in [false, true] {
        let mut elaborator = EffectElaborator::new();
        let pending = elaborator.defer_provider_row(span).unwrap();
        let crate::types::EffectRowVariable::Inference(identity) =
            pending.tail().unwrap().variable()
        else {
            unreachable!()
        };
        assert!(elaborator.cleanup_row_pending(&pending));
        // The actual latest-D host has an empty native interpretation vector.
        // A later owner-native Free cannot become host-interpreted merely by H.
        let outward = elaborator
            .remove_cleanup_effect(&pending, &host_instance(), span, true)
            .unwrap();
        let row_type = Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                Type::Unit,
                crate::types::clone_effect_row_with_budget(
                    &outward,
                    &mut TypeWorkBudget::default(),
                )
                .unwrap(),
            ),
        );
        elaborator
            .defer_resource_escape(host_id, &row_type, span, span)
            .unwrap();
        let mut complete = vec![host_instance()];
        if leave_unlisted_native {
            complete.push(
                crate::core::effect::clone_effect_instance_with_budget(
                    &late,
                    &mut TypeWorkBudget::default(),
                )
                .unwrap(),
            );
        }
        elaborator
            .complete_provider_row(identity, EffectRow::closed(complete.into_boxed_slice()))
            .unwrap();
        elaborator.complete_ready_provider_row_equations().unwrap();
        let settled = elaborator.zonk_effect_row(&outward).unwrap();
        assert!(
            !elaborator.cleanup_row_pending(&settled),
            "exercise equation-drained row"
        );
        assert!(settled.tail().is_none());
        assert_eq!(settled.known().len(), usize::from(leave_unlisted_native));
        assert!(
            elaborator.cleanup_rows.is_empty(),
            "all row equations are drained before publication finalization"
        );
        let result = crate::resolved::ResolvedExpr {
            kind: crate::resolved::ResolvedExprKind::Unit,
            span,
        };
        let mut context = elaborator.base_context.clone();
        let finalized = elaborator.elaborate_result(&result, &mut context);
        if leave_unlisted_native {
            assert_eq!(settled.known()[0].effect(), late.effect());
            let error =
                finalized.expect_err("publication finalizer must reject the late same-H residual");
            assert!(
                matches!(error, TypeError::Source(ref diagnostic) if diagnostic.reason == TypeReason::ResourceEscape),
                "the exact late same-H residual must fail publication's deferred H escape: {error:?}"
            );
        } else {
            finalized.expect("publication finalizer accepts the canonical empty residual after equation draining");
        }
    }
}

// Staged additions to elaborate::checked_owner_lifecycle_tests only.
// Real source parsing and explicit checked resolution must succeed. These
// distinct expected checking boundaries are not interchangeable.
#[test]
fn checked_owner_lifecycle_ordinary_handler_cannot_simulate_native_finish() {
    let canonical = check_graph(&graph(PRODUCER, false)).expect(
        "actual unchanged canonical producer checks before ordinary native-handler refusal",
    );
    assert_producer_originals(&canonical);
    let request = "        let outcome = perform Free<H, R>.call state\n";
    assert_eq!(PRODUCER.matches(request).count(), 1);
    let source = PRODUCER.replace(request,
        "        let outcome = handle (perform Free<H, R>.call state) with Free<H, R> {\n            call ignored => resume (Foreign.CheckedReturned (Foreign.Consumed ()))\n        }\n");
    let error = check_graph(&graph(&source, false))
        .expect_err("ordinary clauses cannot install the original native Free interpreter");
    // finish_handler rejects registry.foreign_effect before checking ordinary
    // clauses. This is its specific authority diagnostic, not a lifecycle-flow
    // Source refusal, and not arbitrary Internal/ForeignContract acceptance.
    assert!(
        matches!(
            error,
            TypeError::Internal(ElaborationFailure::ForeignPrivilegeUnavailable)
        ),
        "expected exact ordinary native-handler authority refusal: {error:?}"
    );
}

#[test]
fn checked_owner_lifecycle_constructed_call_result_does_not_prove_finish_attempt() {
    let canonical = check_graph(&graph(PRODUCER, false))
        .expect("actual unchanged canonical producer checks before constructed-call refusal");
    assert_producer_originals(&canonical);
    let request = "        let outcome = perform Free<H, R>.call state\n";
    assert_eq!(PRODUCER.matches(request).count(), 1);
    let source = PRODUCER.replace(request,
        "        let outcome : Foreign.CheckedCall<Foreign.Disposition<Unit>> = Foreign.CheckedReturned (Foreign.Consumed ())\n");
    // All original exhaustive finish arms and required post-outcome Trace remain
    // intact. Only the attempted native request became ordinary typed data.
    let error = check_graph(&graph(&source, false))
        .expect_err("constructed CheckedCall data cannot supply a native finish-attempt witness");
    assert!(
        matches!(error, TypeError::Source(_)),
        "require semantic source refusal after genuine parsing/resolution, not setup/resource/internal failure: {error:?}"
    );
}

#[path = "checked_scalar_borrow_tests.rs"]
mod checked_scalar_borrow_tests;

/// Shared test-only entry into the existing explicit checked-source pipeline.
/// This never changes the default driver profile or any build/runtime guard.
pub(crate) fn checked_owner_passive_program() -> (
    crate::core::ValidatedEffectProgram,
    Vec<(crate::module::ModuleId, Arc<crate::source::SourceFile>)>,
) {
    let graph = graph(PRODUCER, true);
    let checked = check_graph(&graph).expect("genuine checked source and body-free summaries");
    assert_producer_originals(&checked);
    let linked = link_modules(checked, graph.entry()).expect("genuine checked module link");
    let linked = crate::evidence_validation::validate_interface_evidence(linked)
        .expect("genuine checked module evidence");
    let mut elaborator = EffectElaborator::for_module_program(&linked).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .unwrap();
    let program = elaborator.finish(typed.node).unwrap();
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let core = crate::core::validate_effect_modules(program, &sources, &modules)
        .expect("independent default checked lifecycle Core before passive controls");
    // Retain the literal loaded SourceFile allocations, never equal-text donors.
    let mut work = TypeWorkBudget::default();
    work.charge(graph.modules().len().checked_mul(2).unwrap())
        .unwrap();
    let mut provenance = Vec::new();
    provenance.try_reserve_exact(graph.modules().len()).unwrap();
    for module in graph.modules() {
        provenance.push((module.id(), Arc::clone(module.retained_source())));
    }
    (core, provenance)
}
#[path = "checked_byte_window_tests.rs"]
mod checked_byte_window_tests;
