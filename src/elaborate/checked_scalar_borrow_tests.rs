//! Connected scalar Current Borrow; checked compilation only.

use super::*;

const BORROW_SOURCE: &str = include_str!("../../tests/fixtures/checked-scalar-borrow/owner.ash");
const CONSUMER: &str = "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Foreign.CheckedCall<Int>, Unit, Unit>\nmain () = Producer.run ()\n";

fn canonical(source: &str) -> Vec<CheckedModule> {
    check_graph(&graph_with_entry(source, None))
        .expect("genuine scalar Borrow canonical source and summary must pass first")
}

fn source_refusal(source: &str) {
    canonical(BORROW_SOURCE);
    let error = check_graph(&graph_with_entry(source, None))
        .expect_err("hostile scalar Borrow source must refuse after canonical admission");
    match error {
        TypeError::Source(_) => {}
        TypeError::Internal(ElaborationFailure::ForeignPrivilegeUnavailable) => {}
        error => panic!("expected semantic scalar Borrow refusal, got {error:?}"),
    }
}

#[test]
fn checked_scalar_borrow_source_retains_exact_native_owner_and_assumptions() {
    let checked = canonical(BORROW_SOURCE);
    assert_producer_originals(&checked);
    let producer = checked
        .iter()
        .find(|module| module.source_resource_code().is_some())
        .unwrap();
    let header = producer
        .source_resource_code()
        .unwrap()
        .headers()
        .next()
        .unwrap();
    let read = producer
        .registry()
        .effects()
        .iter()
        .find(|effect| effect.spelling == "Read")
        .unwrap();
    let original = producer
        .registry()
        .native_symbol(crate::types::OperationId::new(read.id, 0))
        .unwrap();
    assert!(Arc::ptr_eq(original.owner().unwrap(), &header.owner));
    assert_eq!(original.parameter_ids().len(), 2);
    assert!(matches!(
        original.owner_role(),
        Some(crate::foreign::source_contract::PreparedOwnerCall::Borrow {
            current_operand: 0,
            ..
        })
    ));
    assert!(original.symbol().access_result().is_none());
    let contract = original.prepared().checked_contract().unwrap();
    let selected = &contract.symbols()[original.symbol_index()];
    assert_eq!(selected.host_parameter(), 0);
    let callee = contract
        .assumptions()
        .iter()
        .find(|assumption| assumption.name() == "Callee")
        .unwrap();
    assert!(
        selected
            .assumption_members()
            .contains(&callee.member_index())
    );
    assert!(
        header
            .original
            .interpreted
            .iter()
            .any(|effect| effect.instance.effect() == original.effect())
    );
    assert!(Arc::ptr_eq(
        producer
            .source_resource_code()
            .unwrap()
            .resource(0)
            .unwrap()
            .original_registry()
            .native_symbol(original.operation())
            .unwrap(),
        original
    ));
}

#[test]
fn checked_scalar_borrow_body_free_consumer_links_core_and_transforms() {
    let graph = graph_with_entry(BORROW_SOURCE, Some(CONSUMER));
    validate_latest_payload_core(&graph);
}

#[test]
fn checked_scalar_borrow_acquisition_phase_does_not_gain_handler_permission() {
    source_refusal(&BORROW_SOURCE.replace(
        "=> Acquired(state, ())",
        "=> {\n let ignored = perform Read<H, R>.call state\n Acquired(state, ())\n }",
    ));
}

#[test]
fn checked_scalar_borrow_finish_phase_does_not_gain_handler_permission() {
    source_refusal(&BORROW_SOURCE.replace(
        "let outcome = perform Free<H, R>.call state",
        "let ignored = perform Read<H, R>.call state\n        let outcome = perform Free<H, R>.call state",
    ));
}

#[test]
fn checked_scalar_borrow_requires_exact_interpreted_membership() {
    source_refusal(&BORROW_SOURCE.replace(
        "interpret Allocate<H, R>, Free<H, R>, Read<H, R>",
        "interpret Allocate<H, R>, Free<H, R>",
    ));
}

#[test]
fn checked_scalar_borrow_handler_requires_exact_host_and_owned_actuals() {
    for actual in ["Int, R", "H, Int", "R, H"] {
        source_refusal(&BORROW_SOURCE.replace(
            "resume (perform Read<H, R>.call state)",
            &format!("resume (perform Read<{actual}>.call state)"),
        ));
    }
}

const INSPECTED_HANDLER: &str = "read access => match perform Read<H, R>.call state {\n            Foreign.CheckedReturned(value) => resume (Foreign.CheckedReturned value)\n            Foreign.CheckedConversionFailed(error) => resume (Foreign.CheckedConversionFailed error)\n            Foreign.BoundaryFailed(reason) => resume (Foreign.BoundaryFailed reason)\n        }";

#[test]
fn checked_scalar_borrow_independent_boundary_result_can_be_forwarded() {
    let source = BORROW_SOURCE.replace(
        "read access => resume (perform Read<H, R>.call state)",
        INSPECTED_HANDLER,
    );
    canonical(&source);
    validate_latest_payload_core(&graph_with_entry(&source, Some(CONSUMER)));
}

#[test]
fn checked_scalar_borrow_failure_branch_cannot_request_native_finish() {
    let source = BORROW_SOURCE.replace(
        "read access => resume (perform Read<H, R>.call state)",
        INSPECTED_HANDLER,
    );
    canonical(&source);
    source_refusal(&source.replace(
        "Foreign.BoundaryFailed(reason) => resume (Foreign.BoundaryFailed reason)",
        "Foreign.BoundaryFailed(reason) => {\n let ignored = perform Free<H, R>.call state\n resume (Foreign.BoundaryFailed reason)\n }",
    ));
}

#[test]
fn checked_scalar_borrow_body_free_reexport_keeps_defining_native_fact() {
    static IDS: AtomicU64 = AtomicU64::new(0);
    struct Owned(std::path::PathBuf);
    impl Drop for Owned {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let directory = loop {
        let path = std::env::temp_dir().join(format!(
            "ash-checked-borrow-reexport-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        match std::fs::create_dir(&path) {
            Ok(()) => break Owned(path),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("create owned Borrow reexport fixture: {error}"),
        }
    };
    std::fs::write(directory.0.join("producer.ash"), BORROW_SOURCE).unwrap();
    std::fs::write(
        directory.0.join("facade.ash"),
        "pub import producer (run as wrapped)\n",
    )
    .unwrap();
    std::fs::write(
        directory.0.join("entry.ash"),
        CONSUMER
            .replace("import producer as Producer", "import facade as Producer")
            .replace("Producer.run", "Producer.wrapped"),
    )
    .unwrap();
    let graph =
        crate::module::load_module_graph(&directory.0.join("entry.ash"), &ModuleRoots::empty())
            .unwrap();
    let checked =
        check_graph(&graph).expect("actual reexport source and body-free summaries authenticate");
    assert_producer_originals(&checked);
    let producer = checked
        .iter()
        .find(|module| module.source_resource_code().is_some())
        .unwrap();
    let read = producer
        .registry()
        .effects()
        .iter()
        .find(|effect| effect.spelling == "Read")
        .unwrap();
    let original = Arc::clone(
        producer
            .registry()
            .native_symbol(crate::types::OperationId::new(read.id, 0))
            .unwrap(),
    );
    let linked = link_modules(checked, graph.entry()).unwrap();
    assert!(Arc::ptr_eq(
        linked
            .registry()
            .native_symbol(original.operation())
            .unwrap(),
        &original
    ));
    validate_latest_payload_core(&graph);
}

fn callback_result_source(capture_state: bool) -> String {
    let boundary_callback = if capture_state {
        "let retained = state\n42"
    } else {
        "42"
    };
    let handler = format!(
        "read access => match perform Read<H, R>.call state {{\n Foreign.CheckedReturned(value) => {{\n let callback : Unit -> Int = fn(ignored) {{ value }}\n resume (Foreign.CheckedReturned callback)\n }}\n Foreign.CheckedConversionFailed(error) => resume (Foreign.CheckedConversionFailed error)\n Foreign.BoundaryFailed(reason) => {{\n let callback : Unit -> Int = fn(ignored) {{ {boundary_callback} }}\n resume (Foreign.CheckedReturned callback)\n }}\n }}"
    );
    BORROW_SOURCE
        .replace(
            "read : Access -> Foreign.CheckedCall<Int>",
            "read : Access -> Foreign.CheckedCall<Unit -> Int>",
        )
        .replace(
            "Foreign.CheckedScope<Foreign.CheckedCall<Int>,",
            "Foreign.CheckedScope<Foreign.CheckedCall<Unit -> Int>,",
        )
        .replace(
            "read access => resume (perform Read<H, R>.call state)",
            &handler,
        )
}

#[test]
fn checked_scalar_borrow_boundary_branch_cannot_transport_current_in_a_callback() {
    canonical(&callback_result_source(false));
    let error = check_graph(&graph_with_entry(&callback_result_source(true), None)).expect_err(
        "the actual independent failure branch cannot transport Current through resume",
    );
    assert!(
        matches!(error, TypeError::Source(_)),
        "semantic failure-branch escape refusal required: {error:?}"
    );
}

#[test]
fn checked_scalar_borrow_no_resource_context_and_ordinary_simulation_refuse() {
    canonical(BORROW_SOURCE);
    let source = format!(
        "{BORROW_SOURCE}\nuncontrolled : State<Int, Bool> -> Foreign.CheckedCall<Int> ! {{Read<Int, Bool>, Foreign.NativeHost<Int>}}\nuncontrolled state = perform Read<Int, Bool>.call state\n"
    );
    let no_context = check_graph(&graph_with_entry(&source, None))
        .expect_err("a native Current request outside its owning phase must refuse");
    assert!(
        matches!(
            no_context,
            TypeError::Internal(ElaborationFailure::ForeignPrivilegeUnavailable)
        ),
        "exact no-context privilege refusal required: {no_context:?}"
    );
    let simulated = BORROW_SOURCE.replace(
        "resume (perform Read<H, R>.call state)",
        "resume (handle (perform Read<H, R>.call state) with Read<H, R> { call ignored => resume (Foreign.CheckedReturned 1) })",
    );
    let error = check_graph(&graph_with_entry(&simulated, None))
        .expect_err("an ordinary native handler cannot simulate a checked Borrow result");
    assert!(
        matches!(
            error,
            TypeError::Internal(ElaborationFailure::ForeignPrivilegeUnavailable)
        ),
        "exact ordinary-handler privilege refusal required: {error:?}"
    );
}

#[test]
fn checked_scalar_borrow_independent_core_checks_read_vectors_membership_and_host_row() {
    let graph = graph_with_entry(BORROW_SOURCE, Some(CONSUMER));
    let checked =
        check_graph(&graph).expect("real scalar Borrow source and body-free consumer first");
    let linked = link_modules(checked, graph.entry()).unwrap();
    let linked = crate::evidence_validation::validate_interface_evidence(linked).unwrap();
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
        .expect("independent actual scalar Borrow Core under default allowance");
    let canonical = crate::core::transform::identity_effect_traversal(&core).unwrap();
    crate::core::source_resource::checked_lifecycle_core_tests::assert_budget_controls(&canonical);
    use crate::core::source_resource::checked_borrow_core_tests::{
        Mutation, mutate_and_authenticate,
    };
    for mutation in [
        Mutation::InterpretationHost,
        Mutation::InterpretationOwned,
        Mutation::MissingInterpretation,
        Mutation::CopiedReadHost,
        Mutation::CopiedReadHostRow,
    ] {
        let mut candidate = crate::core::transform::identity_effect_traversal(&core).unwrap();
        mutate_and_authenticate(&mut candidate, mutation);
        let error = crate::core::validate_effect_modules(candidate, &sources, &modules)
            .expect_err("independent whole Core rejects the hostile exact Read correspondence");
        assert_ne!(
            error.reason(),
            crate::core::ValidationReason::Resource,
            "semantic Borrow Core refusal required for {mutation:?}: {error:?}"
        );
    }
}
