use ash::{
    core::{
        CoreMatchArm, CorePattern, CorePatternKind, EffectClause, EffectCoreBuilder,
        EffectExprKind, HandlerId, Primitive, PureComputation, PureExprKind, ResumeUse,
        ValidatedEffectProgram, validate_effect_modules,
    },
    elaborate::{EffectElaborator, check_module, link_modules},
    eval::{EffectTraceEvent, evaluate_effect},
    evidence_validation::validate_interface_evidence,
    integer::Integer,
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{CheckedModule, ResumeId},
    source::{ByteRange, Origin, SourceFile},
    types::{EffectInstance, EffectRow, Type},
};
use std::path::Path;

fn check_graph(graph: &ModuleGraph) -> Vec<CheckedModule> {
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency: &&CheckedModule| dependency.module() == edge.target())
                    .expect("dependencies precede importers");
                DependencyExports::new(edge, dependency.exports()).expect("authenticated exports")
            })
            .collect::<Vec<_>>();
        checked.push(
            check_module(resolve_module(module, &dependencies).expect("resolved module"))
                .expect("checked module"),
        );
    }
    checked
}

fn effect_program(path: &Path) -> ValidatedEffectProgram {
    let graph = load_module_graph(path, &ModuleRoots::empty()).expect("fixture should load");
    let linked = link_modules(check_graph(&graph), graph.entry()).expect("fixture should link");
    let linked = validate_interface_evidence(linked).expect("evidence should authenticate");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("builder should start");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("effects should lower");
    let unchecked = elaborator.finish(typed.node).expect("Core should finish");
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
    validate_effect_modules(unchecked, &sources, &module_sources).expect("Core should validate")
}

fn run_effect_source(name: &str, source: &str) -> ash::eval::Evaluation {
    let path = std::env::temp_dir().join(format!(
        "ash-effect-runtime-{name}-{}-{}.ash",
        std::process::id(),
        SourceFile::new(name, "")
            .expect("source identity")
            .id()
            .value()
    ));
    std::fs::write(&path, source).expect("effect runtime fixture should be writable");
    let evaluation = evaluate_effect(&effect_program(&path)).expect("effect Core should execute");
    let _ = std::fs::remove_file(path);
    evaluation
}

#[test]
fn discard_abandons_suspended_addition_and_continues_the_clause() {
    let evaluation = run_effect_source(
        "discard-addition",
        concat!(
            "effect Ask {\nask : Unit -> Int\n}\n\n",
            "main : Unit -> Int\n",
            "main () = handle (perform Ask.ask () + 100) with Ask {\n",
            "ask ignored => {\nlet () = discard\n40 + 2\n}\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
    assert!(matches!(evaluation.effect_trace(), [
        EffectTraceEvent::HandlerActivated(handler),
        EffectTraceEvent::Request(operation),
        EffectTraceEvent::HandlerSelected(selected),
        EffectTraceEvent::ClauseEntered(clause, requested),
        EffectTraceEvent::Discard(discarded),
        EffectTraceEvent::ClauseReturned(returned),
    ] if handler == selected && handler == clause && handler == discarded && handler == returned && operation == requested));
}

#[test]
fn discard_preserves_surrounding_handler_work_without_running_suspended_requests() {
    let evaluation = run_effect_source(
        "discard-surrounding",
        concat!(
            "effect Ask {\nask : Unit -> Int\n}\n\n",
            "effect Mark {\nmark : Int -> Int\n}\n\n",
            "main : Unit -> Int\nmain () = handle ({\n",
            "let result = handle ({\nlet _ = perform Ask.ask ()\n",
            "perform Mark.mark 999\n}) with Ask {\n",
            "ask ignored => {\nlet _ = discard\n40\n}\n}\n",
            "perform Mark.mark result\n}) with Mark {\n",
            "mark value => resume (value + 2)\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
    assert!(matches!(evaluation.effect_trace(), [
        EffectTraceEvent::HandlerActivated(outer),
        EffectTraceEvent::HandlerActivated(inner),
        EffectTraceEvent::Request(ask),
        EffectTraceEvent::HandlerSelected(selected_inner),
        EffectTraceEvent::ClauseEntered(inner_clause, requested_ask),
        EffectTraceEvent::Discard(discarded),
        EffectTraceEvent::ClauseReturned(inner_returned),
        EffectTraceEvent::Request(mark),
        EffectTraceEvent::HandlerSelected(selected_outer),
        EffectTraceEvent::ClauseEntered(outer_clause, requested_mark),
        EffectTraceEvent::Resume(resumed),
        EffectTraceEvent::HandlerRestored(restored),
        EffectTraceEvent::ClauseReturned(outer_returned),
    ] if inner == selected_inner && inner == inner_clause && inner == discarded && inner == inner_returned
        && outer == selected_outer && outer == outer_clause && outer == resumed && outer == restored && outer == outer_returned
        && outer != inner && ask == requested_ask && mark == requested_mark));
}

#[test]
fn inner_discard_leaves_the_outer_live_owner_available_to_resume() {
    let evaluation = run_effect_source(
        "discard-inside-live-clause",
        concat!(
            "effect Ask {\nask : Unit -> Int\n}\n\n",
            "effect Mark {\nmark : Unit -> Int\n}\n\n",
            "main : Unit -> Int\n",
            "main () = handle (perform Ask.ask () + 100) with Ask {\n",
            "ask ignored => {\n",
            "let value = handle (perform Mark.mark ()) with Mark {\n",
            "mark ignored => {\nlet _ = discard\n40\n}\n}\n",
            "resume (value + 2)\n}\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "142");
    let completion = evaluation
        .effect_trace()
        .iter()
        .filter(|event| {
            matches!(
                event,
                EffectTraceEvent::Resume(_) | EffectTraceEvent::Discard(_)
            )
        })
        .copied()
        .collect::<Vec<_>>();
    assert!(
        matches!(completion.as_slice(), [EffectTraceEvent::Discard(inner), EffectTraceEvent::Resume(outer)] if inner != outer)
    );
}

#[test]
fn outward_discard_can_abandon_an_already_consumed_clause_boundary() {
    let evaluation = run_effect_source(
        "discard-consumed-clause",
        concat!(
            "effect Ask {\nask : Unit -> Int\n}\n\n",
            "effect Mark {\nmark : Int -> Int\n}\n\n",
            "main : Unit -> Int\nmain () = handle (\n",
            "handle (perform Ask.ask ()) with Ask {\n",
            "ask ignored => {\nlet _ = resume 0\n",
            "let _ = perform Mark.mark 41\n999\n}\n}\n",
            ") with Mark {\nmark value => {\nlet _ = discard\nvalue + 1\n}\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
    let returned = evaluation
        .effect_trace()
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::ClauseReturned(handler) => Some(*handler),
            _ => None,
        })
        .collect::<Vec<_>>();
    let discarded = evaluation
        .effect_trace()
        .iter()
        .find_map(|event| match event {
            EffectTraceEvent::Discard(handler) => Some(*handler),
            _ => None,
        })
        .expect("outer handler discards");
    assert_eq!(returned, [discarded]);
}

#[test]
fn mixed_completion_branches_resume_or_discard_the_selected_request() {
    for (argument, expected, resumes) in [("true", "42", 0), ("false", "101", 1)] {
        let source = format!(
            "effect Ask {{\nask : Bool -> Int\n}}\n\n\
             main : Unit -> Int\n\
             main () = handle (perform Ask.ask {argument} + 100) with Ask {{\n\
             ask choice => match choice {{\n\
             true => {{\nlet _ = discard\n42\n}}\n\
             false => resume 1\n}}\n}}\n"
        );
        let evaluation = run_effect_source("mixed-completion", &source);
        assert_eq!(evaluation.value.to_string(), expected);
        assert_eq!(
            evaluation
                .effect_trace()
                .iter()
                .filter(|event| matches!(event, EffectTraceEvent::Resume(_)))
                .count(),
            resumes
        );
    }
}

#[test]
fn handled_request_preserves_erased_newtype_values_across_resume() {
    let evaluation = run_effect_source(
        "newtype-resume",
        concat!(
            "newtype UserId = UserId(Int)\n\n",
            "effect Relay {\nbounce : UserId -> UserId\n}\n\n",
            "main : Unit -> Int\n",
            "main () = {\n",
            "let wrapped = handle (perform Relay.bounce (UserId(41))) with Relay {\n",
            "bounce UserId(value) => resume (UserId(value + 1))\n",
            "}\n",
            "match wrapped {\nUserId(value) => value\n}\n",
            "}\n",
        ),
    );

    assert_eq!(evaluation.value.to_string(), "42");
    assert!(matches!(
        evaluation.effect_trace(),
        [
            EffectTraceEvent::HandlerActivated(_),
            EffectTraceEvent::Request(_),
            EffectTraceEvent::HandlerSelected(_),
            EffectTraceEvent::ClauseEntered(_, _),
            EffectTraceEvent::Resume(_),
            EffectTraceEvent::HandlerRestored(_),
            EffectTraceEvent::ClauseReturned(_),
        ]
    ));
}

#[test]
fn local_nominal_scope_is_static_in_effect_core() {
    let source = concat!(
        "effect Ask {\nask : Unit -> Int\n}\n\n",
        "main : Unit -> Int\n",
        "main () = {\n",
        "newtype Offset = Offset(Int)\n",
        "let offset = Offset(41)\n",
        "handle (perform Ask.ask ()) with Ask {\n",
        "ask ignored => resume (match offset {\n",
        "Offset(value) => value + 1\n",
        "})\n",
        "}\n",
        "}\n",
    );
    let path = std::env::temp_dir().join(format!(
        "ash-effect-runtime-local-scope-{}-{}.ash",
        std::process::id(),
        SourceFile::new("local-scope", "")
            .expect("source identity")
            .id()
            .value()
    ));
    std::fs::write(&path, source).expect("effect local-scope fixture should be writable");
    let program = effect_program(&path);
    let _ = std::fs::remove_file(path);

    let mut pending = vec![program.root()];
    let mut scopes = 0;
    while let Some(id) = pending.pop() {
        let node = program.node(id).expect("reachable effect Core node");
        if matches!(
            &node.kind,
            EffectExprKind::Pure(PureExprKind::Computation(
                PureComputation::LocalNominalScope(_)
            ))
        ) {
            scopes += 1;
        }
        pending.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
    }
    assert_eq!(scopes, 1);

    let evaluation = evaluate_effect(&program).expect("effect local scope should execute");
    assert_eq!(evaluation.value.to_string(), "42");
    assert!(
        evaluation
            .effect_trace()
            .iter()
            .any(|event| matches!(event, EffectTraceEvent::Resume(_)))
    );
}

#[test]
fn nested_forwarding_restores_intervening_handlers_in_original_order() {
    let source = concat!(
        "effect Ask {\nask : Int -> Int\n}\n\n",
        "effect Mark {\nmark : Int -> Int\n}\n\n",
        "main : Unit -> Int\n",
        "main () = handle (\n",
        "handle ({\nlet answered = perform Ask.ask 1\nperform Mark.mark answered\n}) with Mark {\n",
        "mark value => resume (value + 10)\n",
        "}\n",
        ") with Ask {\n",
        "ask value => {\nlet continued = resume (value + 1)\ncontinued + 100\n}\n",
        "}\n",
    );
    let path = std::env::temp_dir().join(format!(
        "ash-effect-runtime-red-{}-{}.ash",
        std::process::id(),
        SourceFile::new("effect-runtime-red", "")
            .expect("source identity")
            .id()
            .value()
    ));
    std::fs::write(&path, source).expect("effect runtime fixture should be writable");
    let evaluation =
        evaluate_effect(&effect_program(&path)).expect("validated Core should execute");
    let _ = std::fs::remove_file(path);
    assert_eq!(evaluation.value.to_string(), "112");
    let boundaries = evaluation.effect_trace();
    let [
        EffectTraceEvent::HandlerActivated(outer),
        EffectTraceEvent::HandlerActivated(inner),
        EffectTraceEvent::Request(ask),
        ..,
    ] = boundaries
    else {
        panic!("handler trace should begin with outer, inner, request: {boundaries:?}")
    };
    let mark = match boundaries.get(8) {
        Some(EffectTraceEvent::Request(operation)) => *operation,
        _ => panic!("restored inner request should follow restoration: {boundaries:?}"),
    };
    assert_eq!(
        boundaries,
        [
            EffectTraceEvent::HandlerActivated(*outer),
            EffectTraceEvent::HandlerActivated(*inner),
            EffectTraceEvent::Request(*ask),
            EffectTraceEvent::HandlerSelected(*outer),
            EffectTraceEvent::ClauseEntered(*outer, *ask),
            EffectTraceEvent::Resume(*outer),
            EffectTraceEvent::HandlerRestored(*outer),
            EffectTraceEvent::HandlerRestored(*inner),
            EffectTraceEvent::Request(mark),
            EffectTraceEvent::HandlerSelected(*inner),
            EffectTraceEvent::ClauseEntered(*inner, mark),
            EffectTraceEvent::Resume(*inner),
            EffectTraceEvent::HandlerRestored(*inner),
            EffectTraceEvent::ClauseReturned(*inner),
            EffectTraceEvent::ClauseReturned(*outer),
        ]
    );
}

#[test]
fn nearest_delegation_and_sequential_requests_preserve_clause_control() {
    let evaluation = run_effect_source(
        "delegation",
        concat!(
            "effect Ask {\nask : Int -> Int\n}\n\n",
            "main : Unit -> Int\n",
            "main () = handle (\n",
            "handle ({\nlet first = perform Ask.ask 1\nperform Ask.ask first\n}) with Ask {\n",
            "ask value => {\nlet delegated = perform Ask.ask value\nresume delegated\n}\n",
            "}\n",
            ") with Ask {\nask value => resume (value + 1)\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "3");
    let selected = evaluation
        .effect_trace()
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::HandlerSelected(handler) => Some(*handler),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(selected.len(), 4);
    assert_eq!(selected[0], selected[2]);
    assert_eq!(selected[1], selected[3]);
    assert_ne!(selected[0], selected[1]);
}

#[test]
fn distinct_parameterized_instances_select_exact_handlers() {
    let evaluation = run_effect_source(
        "parameterized",
        concat!(
            "effect Read<A> {\nread : Unit -> A\n}\n\n",
            "main : Unit -> Int\n",
            "main () = handle (\n",
            "handle ({\nlet number = perform Read<Int>.read ()\n",
            "let ignored = perform Read<Bool>.read ()\nnumber\n}) with Read<Bool> {\n",
            "read ignored => resume true\n}\n",
            ") with Read<Int> {\nread ignored => resume 42\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
    let selected = evaluation
        .effect_trace()
        .iter()
        .filter(|event| matches!(event, EffectTraceEvent::HandlerSelected(_)))
        .count();
    assert_eq!(selected, 2);
}

#[test]
fn clause_request_bypasses_captured_intervening_handler() {
    let evaluation = run_effect_source(
        "clause-bypass",
        concat!(
            "effect Ask {\nask : Int -> Int\n}\n\n",
            "effect Mark {\nmark : Int -> Int\n}\n\n",
            "main : Unit -> Int\n",
            "main () = handle (\nhandle (\nhandle ({\n",
            "let answered = perform Ask.ask 1\nperform Mark.mark answered\n",
            "}) with Mark {\nmark value => resume (value + 10)\n}\n",
            ") with Ask {\nask value => {\n",
            "let outside = perform Mark.mark value\nresume outside\n}\n}\n",
            ") with Mark {\nmark value => resume (value + 100)\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "111");
    let selected = evaluation
        .effect_trace()
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::HandlerSelected(handler) => Some(*handler),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(selected.len(), 3);
    assert_ne!(selected[1], selected[2]);
}

#[test]
fn deep_forwarded_continuation_executes_on_a_small_host_stack() {
    const ADDITIONS: usize = 4_096;
    let worker = std::thread::Builder::new()
        .name("deep-effect-machine".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let source = concat!(
                "effect Ask {\nask : Int -> Int\n}\n\n",
                "effect Mark {\nmark : Int -> Int\n}\n\n",
                "main : Unit -> Int\nmain () = 0\n",
            );
            let path = std::env::temp_dir().join(format!(
                "ash-effect-runtime-deep-{}-{}.ash",
                std::process::id(),
                SourceFile::new("deep-runtime", "")
                    .expect("source identity")
                    .id()
                    .value()
            ));
            std::fs::write(&path, source).expect("deep fixture should be writable");
            let graph = load_module_graph(&path, &ModuleRoots::empty()).expect("fixture loads");
            let checked = check_graph(&graph);
            let registry = checked[0].registry().clone();
            let ask = &checked[0].effects()[0];
            let mark = &checked[0].effects()[1];
            let ask_instance = EffectInstance::new(ask.id, Box::new([]));
            let mark_instance = EffectInstance::new(mark.id, Box::new([]));
            let origin = Origin::Source(
                graph.modules()[0]
                    .source()
                    .span(ByteRange::new(0, source.len() as u32).expect("ordered range"))
                    .expect("source span"),
            );
            let mut builder = EffectCoreBuilder::with_effect_registry(registry);
            let zero = builder
                .integer(
                    Integer::parse_decimal("0").expect("integer"),
                    Type::Int,
                    origin.clone(),
                )
                .expect("zero should fit");
            let mut deep = builder
                .request(
                    ask_instance.clone(),
                    ask.operations[0].id,
                    zero,
                    Type::Int,
                    EffectRow::singleton(ask_instance.clone()),
                    origin.clone(),
                )
                .expect("request should fit");
            for _ in 0..ADDITIONS {
                let one = builder
                    .integer(
                        Integer::parse_decimal("1").expect("integer"),
                        Type::Int,
                        origin.clone(),
                    )
                    .expect("one should fit");
                deep = builder
                    .primitive(Primitive::Add, deep, one, Type::Int, origin.clone())
                    .expect("addition should fit");
            }
            let body = builder
                .request(
                    mark_instance.clone(),
                    mark.operations[0].id,
                    deep,
                    Type::Int,
                    EffectRow::closed(
                        vec![ask_instance.clone(), mark_instance.clone()].into_boxed_slice(),
                    ),
                    origin.clone(),
                )
                .expect("forwarded request should fit");
            let mark_binder = builder.binder(Type::Int, origin.clone()).expect("binder");
            let mark_value = builder
                .variable(mark_binder.id(), Type::Int, origin.clone())
                .expect("clause value");
            let mark_resume = builder
                .resume(
                    HandlerId::new(1),
                    ResumeId::new(1),
                    ResumeUse::Consumed,
                    mark_value,
                    Type::Int,
                    EffectRow::singleton(ask_instance.clone()),
                    origin.clone(),
                )
                .expect("mark resume");
            let inner = builder
                .handler(
                    HandlerId::new(1),
                    body,
                    mark_instance,
                    vec![EffectClause::new(
                        mark.operations[0].id,
                        ResumeId::new(1),
                        CoreMatchArm::new(
                            CorePattern::new(
                                Type::Int,
                                origin.clone(),
                                CorePatternKind::Binder(mark_binder),
                            ),
                            mark_resume,
                            origin.clone(),
                        ),
                    )],
                    Type::Int,
                    EffectRow::singleton(ask_instance.clone()),
                    origin.clone(),
                )
                .expect("inner handler");
            let ask_binder = builder.binder(Type::Int, origin.clone()).expect("binder");
            let ask_value = builder
                .variable(ask_binder.id(), Type::Int, origin.clone())
                .expect("clause value");
            let ask_resume = builder
                .resume(
                    HandlerId::new(0),
                    ResumeId::new(0),
                    ResumeUse::Consumed,
                    ask_value,
                    Type::Int,
                    EffectRow::empty(),
                    origin.clone(),
                )
                .expect("ask resume");
            let root = builder
                .handler(
                    HandlerId::new(0),
                    inner,
                    ask_instance,
                    vec![EffectClause::new(
                        ask.operations[0].id,
                        ResumeId::new(0),
                        CoreMatchArm::new(
                            CorePattern::new(
                                Type::Int,
                                origin.clone(),
                                CorePatternKind::Binder(ask_binder),
                            ),
                            ask_resume,
                            origin.clone(),
                        ),
                    )],
                    Type::Int,
                    EffectRow::empty(),
                    origin,
                )
                .expect("outer handler");
            let program = ash::core::validate_effect(
                builder.finish(root).expect("Core should finish"),
                &[graph.modules()[0].source()],
            )
            .expect("deep Core should validate");
            let evaluation = evaluate_effect(&program).expect("deep Core should execute");
            let _ = std::fs::remove_file(path);
            (evaluation.value.to_string(), evaluation.max_frame_depth)
        })
        .expect("small-stack effect worker should spawn");
    let (value, depth) = worker.join().expect("effect machine must remain iterative");
    assert_eq!(value, ADDITIONS.to_string());
    assert!(depth >= ADDITIONS);
}
