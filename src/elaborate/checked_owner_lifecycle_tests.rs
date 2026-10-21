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
        for consumer in checked.iter().filter(|module| {
            module.module() != producer.module()
                && module
                    .direct_dependencies()
                    .iter()
                    .any(|edge| edge.target() == producer.module())
        }) {
            let imported = consumer
                .registry()
                .native_symbol(original.operation())
                .expect("real passive consumer retains the captured native original");
            assert!(Arc::ptr_eq(imported, original));
            let retained = consumer
                .registry()
                .source_resource_fact(header.id)
                .expect("real passive consumer retains the required resource header");
            assert!(Arc::ptr_eq(retained, header));
        }
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
    let linked =
        link_modules(checked, graph.entry()).expect("canonical lifecycle module closure links");
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
        "Foreign.BoundaryFailed(reason) => {\n                let ignored = Foreign.data_of<State<H, R>, Unit> state\n                Foreign.FinishedBoundary reason\n            }",
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
