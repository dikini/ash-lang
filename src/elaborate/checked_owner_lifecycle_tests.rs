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
    static IDS: AtomicU64 = AtomicU64::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-checked-owner-lifecycle-{}-{}",
        std::process::id(),
        IDS.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    std::fs::write(directory.join("producer.ash"), producer).unwrap();
    let entry = if consumer {
        std::fs::write(directory.join("entry.ash"), "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Int, Unit, Unit>\nmain () = Producer.run ()\n").unwrap();
        directory.join("entry.ash")
    } else {
        directory.join("producer.ash")
    };
    let graph = crate::module::load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    std::fs::remove_dir_all(&directory).unwrap();
    graph
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
    let error = check_graph(&graph(&changed, false))
        .err()
        .expect("changed checked finish must be rejected");
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
        .err()
        .expect("changed retained teardown finish must be rejected");
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

// Intended as a staged extension of the existing private lifecycle tests.
// The fragment uses existing graph(source, false) and check_graph helpers.
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
        let local = format!("{producer}{within}");
        check_graph(&graph(&local, false)).expect(
            "replacement E is usable while its distinct outer ordinary owner C remains live",
        );
        // The escaping control is legal when the stored replacement callback
        // is independent, distinguishing the latest E edge from blanket refusal.
        let independent =
            format!("{producer}{escape}").replace("let retained = outer", "let retained = 1");
        check_graph(&graph(&independent, false))
            .expect("an independent latest callback permits the report to leave C");
        let changed = format!("{producer}{escape}");
        let error = check_graph(&graph(&changed, false))
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
    let source = PRODUCER.replace("note ignored => resume ()", "note ignored => discard");
    let error = check_graph(&graph(&source, false))
        .err()
        .expect("required post-finish source continuation cannot be abandoned");
    assert!(
        matches!(error, TypeError::Source(_)),
        "semantic refusal required: {error:?}"
    );
}
