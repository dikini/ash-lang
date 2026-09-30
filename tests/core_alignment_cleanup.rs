//! Bounded cleanup comparison fixtures for the one-shot design experiment.
//! Current source admission excludes the retained-handler raw calculus trace.

use ash::{
    core::{ValidatedEffectProgram, validate_effect_modules},
    driver::{RunConfiguration, run_path},
    elaborate::{EffectElaborator, check_module, link_modules},
    eval::{EffectTraceEvent, Evaluation, evaluate_effect},
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
};
use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("docs/design/direct-effects/one-shot/fixtures")
        .join(format!("core-cleanup-{name}.ash"))
}

fn driver_result(name: &str) -> Result<String, String> {
    run_path(RunConfiguration {
        entry: fixture(name),
        roots: ModuleRoots::empty(),
    })
    .map(|observation| observation.value_display())
    .map_err(|failure| failure.reason_code())
}

fn effect_program(name: &str) -> ValidatedEffectProgram {
    let graph = load_module_graph(&fixture(name), &ModuleRoots::empty()).expect("fixture loads");
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency| dependency.module() == edge.target())
                    .expect("dependencies precede importers");
                DependencyExports::new(edge, dependency.exports()).expect("exports authenticate")
            })
            .collect::<Vec<_>>();
        checked.push(
            check_module(resolve_module(module, &dependencies).expect("fixture resolves"))
                .expect("fixture checks"),
        );
    }
    let linked = link_modules(checked, graph.entry()).expect("fixture links");
    let linked = validate_interface_evidence(linked).expect("interface evidence authenticates");
    let mut elaborator = EffectElaborator::for_module_program(&linked).expect("builder starts");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("effects lower");
    let core = elaborator.finish(typed.node).expect("Core finishes");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    validate_effect_modules(core, &sources, &module_sources).expect("Core independently validates")
}

fn evaluation(name: &str) -> Evaluation {
    evaluate_effect(&effect_program(name)).expect("validated fixture executes")
}

#[test]
fn removed_cleanup_interpreter_is_rejected_even_with_an_outside_copy() {
    // The exact minimal calculus shape first fails the outward cleanup row gate.
    assert_eq!(
        driver_result("removed-handler"),
        Err("effect.row-union-ambiguous".into())
    );
    // Supplying the outward row isolates the forbidden nearest-handler fallback.
    assert_eq!(
        driver_result("outside-copy"),
        Err("effect.cleanup-context".into())
    );
}

#[test]
fn surviving_outer_interpreter_handles_cleanup_after_discard() {
    assert_eq!(driver_result("surviving-handler"), Ok("()".into()));
    let evaluation = evaluation("surviving-handler");
    let events = evaluation.effect_trace();
    let activated = events
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::HandlerActivated(handler) => Some(*handler),
            _ => None,
        })
        .collect::<Vec<_>>();
    let selected = events
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::HandlerSelected(handler) => Some(*handler),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(activated.len(), 2);
    assert_eq!(selected, vec![activated[1], activated[0]]);
    assert!(events.contains(&EffectTraceEvent::Discard(activated[1])));
    assert!(events.contains(&EffectTraceEvent::Resume(activated[0])));
}

#[test]
fn passed_body_handler_does_not_replace_the_cleanup_interpreter() {
    assert_eq!(driver_result("passed-body-handler"), Ok("()".into()));
    let evaluation = evaluation("passed-body-handler");
    let events = evaluation.effect_trace();
    let activated = events
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::HandlerActivated(handler) => Some(*handler),
            _ => None,
        })
        .collect::<Vec<_>>();
    let selected = events
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::HandlerSelected(handler) => Some(*handler),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(activated.len(), 3);
    assert_eq!(selected, vec![activated[2], activated[1], activated[0]]);
}

#[test]
fn nested_cleanup_reads_live_cells_and_closes_innermost_first() {
    // Discard skips body digit 4, closes 2 then 1, and continues the clause at 3.
    // Resume executes digit 4, then the same 2/1 cleanup order and clause digit 3.
    for (name, expected, writes) in [
        ("nested-discard", "70213", 3),
        ("nested-resume", "424213", 4),
    ] {
        assert_eq!(driver_result(name), Ok(expected.into()), "{name}");
        let evaluation = evaluation(name);
        assert_eq!(evaluation.value.to_string(), expected);
        let events = evaluation.effect_trace();
        let acquired = events
            .iter()
            .filter_map(|event| match event {
                EffectTraceEvent::ResourceAcquired(key) => Some(*key),
                _ => None,
            })
            .collect::<Vec<_>>();
        let released = events
            .iter()
            .filter_map(|event| match event {
                EffectTraceEvent::ResourceReleased(key) => Some(*key),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(acquired.len(), 3);
        assert_eq!(released, acquired.iter().rev().copied().collect::<Vec<_>>());
        assert_eq!(
            events
                .iter()
                .filter(|event| matches!(event,
            EffectTraceEvent::ResourceWritten(key) if *key == acquired[0]))
                .count(),
            writes
        );
        let cell_events = events
            .iter()
            .copied()
            .filter(|event| {
                matches!(
                    event,
                    EffectTraceEvent::ResourceAcquired(_)
                        | EffectTraceEvent::ResourceRead(_)
                        | EffectTraceEvent::ResourceWritten(_)
                        | EffectTraceEvent::ResourceReleased(_)
                )
            })
            .collect::<Vec<_>>();
        use EffectTraceEvent::{
            ResourceAcquired as Acquire, ResourceRead as Read, ResourceReleased as Release,
            ResourceWritten as Write,
        };
        let [trace, outer, inner] = acquired.as_slice() else {
            panic!("three cells")
        };
        let mut expected_cells = vec![Acquire(*trace), Acquire(*outer), Acquire(*inner)];
        if name == "nested-resume" {
            expected_cells.extend([Read(*trace), Write(*trace)]);
        }
        expected_cells.extend([
            Read(*trace),
            Read(*inner),
            Write(*trace),
            Release(*inner),
            Read(*trace),
            Read(*outer),
            Write(*trace),
            Release(*outer),
            Read(*trace),
            Write(*trace),
            Read(*trace),
            Release(*trace),
        ]);
        assert_eq!(cell_events, expected_cells, "{name}");
    }
}

#[test]
fn nested_discard_preserves_the_restored_clause_suffix() {
    assert_eq!(driver_result("restored-clause-suffix"), Ok("11".into()));
    let program = effect_program("restored-clause-suffix");
    let evaluation = evaluate_effect(&program).expect("validated fixture executes");
    // The three write applications have pure literal tuple arguments. Node-entry
    // observations distinguish cleanup 7, restored suffix 11, and skipped 99.
    use ash::core::{EffectExprKind, PureComputation, PureExprKind, PureValue};
    let mut pending = vec![program.root()];
    let mut seen = std::collections::HashSet::new();
    let mut writes = std::collections::HashMap::new();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        let node = program.node(id).expect("reachable Core node");
        if let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) =
            &node.kind
            && let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Tuple(tuple))) =
                &program
                    .node(application.argument())
                    .expect("application argument")
                    .kind
            && let [_, value] = tuple.elements()
            && let EffectExprKind::Pure(PureExprKind::Value(PureValue::Integer(literal))) =
                &program.node(*value).expect("write value").kind
        {
            writes.insert(id, literal.value().to_string());
        }
        pending.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
    }
    let mut literals = writes.values().map(String::as_str).collect::<Vec<_>>();
    literals.sort_unstable();
    assert_eq!(literals, vec!["11", "7", "99"]);
    let entered_writes = evaluation
        .trace
        .iter()
        .filter_map(|event| match event {
            ash::eval::TraceEvent::Enter(id) => writes.get(id).map(String::as_str),
        })
        .collect::<Vec<_>>();
    assert_eq!(entered_writes, vec!["7", "11"]);
    assert_eq!(evaluation.value.to_string(), "11");
    let events = evaluation.effect_trace();
    assert_eq!(
        events
            .iter()
            .filter(|event| matches!(event, EffectTraceEvent::ResourceWritten(_)))
            .count(),
        2
    );
    let consumed = events
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::Resume(handler) => Some(("resume", *handler)),
            EffectTraceEvent::Discard(handler) => Some(("discard", *handler)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(consumed.len(), 2);
    assert_eq!(consumed[0].0, "resume");
    assert_eq!(consumed[1].0, "discard");
    assert_eq!(consumed[0].1, consumed[1].1);
}

#[test]
fn pure_closure_can_capture_a_cell_while_its_owner_remains_live() {
    assert_eq!(driver_result("pure-closure-capture"), Ok("()".into()));
    let evaluation = evaluation("pure-closure-capture");
    assert_eq!(evaluation.value.to_string(), "()");
    assert_eq!(
        evaluation.effect_trace(),
        &[
            EffectTraceEvent::ResourceAcquired(0),
            EffectTraceEvent::ResourceReleased(0),
        ]
    );
}

#[test]
fn same_operation_accepts_distinct_pure_closure_bodies_in_validated_core() {
    use ash::{
        core::{EffectExprKind, EffectOperation, PureComputation, PureExprKind, PureValue},
        types::Type,
    };

    #[derive(Debug, PartialEq, Eq)]
    enum BodyShape {
        Unit,
        Bind,
    }

    // The independent validator runs before inspecting the lowered requests.
    let program = effect_program("passed-distinct-closures");
    let mut pending = vec![program.root()];
    let mut seen = std::collections::HashSet::new();
    let mut payloads = Vec::new();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        let node = program.node(id).expect("reachable Core node");
        if let EffectExprKind::Operation(EffectOperation::Request(request)) = &node.kind {
            let operand = program.node(request.operand()).expect("request operand");
            let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) =
                &operand.kind
            else {
                panic!("Invoke.run operand must remain a Core function");
            };
            let body = program.node(function.body()).expect("closure body");
            let shape = match &body.kind {
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Unit(_))) => BodyShape::Unit,
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(_))) => {
                    BodyShape::Bind
                }
                _ => panic!("unexpected closure body: {:?}", body.kind),
            };
            payloads.push((request.effect(), request.operation(), &operand.ty, shape));
        }
        pending.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
    }
    assert_eq!(payloads.len(), 2, "both requests survive lowering");
    assert_eq!(payloads[0].0, payloads[1].0, "same exact effect instance");
    assert_eq!(payloads[0].1, payloads[1].1, "same exact operation");
    assert_eq!(payloads[0].2, payloads[1].2, "same declared payload type");
    assert_eq!(payloads[0].2, &Type::function(Type::Unit, Type::Unit));
    assert_ne!(payloads[0].3, payloads[1].3, "Unit and Bind body shapes");

    let evaluation = evaluate_effect(&program).expect("validated fixture executes");
    assert_eq!(evaluation.value.to_string(), "()");
    assert_eq!(
        evaluation
            .effect_trace()
            .iter()
            .filter(|event| matches!(event, EffectTraceEvent::Request(_)))
            .count(),
        2,
        "both same-key requests execute"
    );
}

#[test]
fn pure_closure_payload_executes_inside_its_cell_owner() {
    assert_eq!(driver_result("passed-pure-closure"), Ok("()".into()));
    let evaluation = evaluation("passed-pure-closure");
    assert_eq!(evaluation.value.to_string(), "()");
    let cell_events = evaluation
        .effect_trace()
        .iter()
        .copied()
        .filter(|event| {
            matches!(
                event,
                EffectTraceEvent::ResourceAcquired(_) | EffectTraceEvent::ResourceReleased(_)
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        cell_events,
        vec![
            EffectTraceEvent::ResourceAcquired(0),
            EffectTraceEvent::ResourceReleased(0),
        ]
    );
}

#[test]
fn pure_closure_payload_cannot_cross_outside_its_cell_owner() {
    assert_eq!(
        driver_result("passed-pure-closure-outside"),
        Err("type.resource-escape".into())
    );
}

#[test]
fn ordinary_helper_accepts_distinct_closures_and_both_branch_results() {
    assert_eq!(driver_result("helper-closure-branch"), Ok("()".into()));
    let evaluation = evaluation("helper-closure-branch");
    assert_eq!(evaluation.value.to_string(), "()");
    assert_eq!(
        evaluation.effect_trace(),
        &[
            EffectTraceEvent::ResourceAcquired(0),
            EffectTraceEvent::ResourceReleased(0),
        ]
    );
}
