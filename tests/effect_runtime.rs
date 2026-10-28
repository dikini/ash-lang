use ash::{
    core::{
        CoreMatchArm, CorePattern, CorePatternKind, EffectClause, EffectCoreBuilder,
        EffectExprKind, EffectOperation, HandlerId, Primitive, PureComputation, PureExprKind,
        ResumeUse, ValidatedEffectProgram, validate_effect_modules,
    },
    elaborate::{EffectElaborator, check_module, link_modules},
    eval::{EffectTraceEvent, evaluate_effect},
    evidence_validation::validate_interface_evidence,
    integer::Integer,
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{CheckedModule, ResumeId},
    source::{ByteRange, Origin, SourceFile},
    types::{EffectId, EffectInstance, EffectRow, OperationId, Type},
};
use std::{
    collections::{HashMap, HashSet},
    path::Path,
};

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

struct TraceOperations {
    allocation_effect: EffectId,
    allocation: Vec<OperationId>,
    source: Vec<OperationId>,
}

fn effect_program(path: &Path) -> ValidatedEffectProgram {
    effect_program_with_trace_operations(path).0
}

fn effect_program_with_trace_operations(path: &Path) -> (ValidatedEffectProgram, TraceOperations) {
    let graph = load_module_graph(path, &ModuleRoots::empty()).expect("fixture should load");
    let checked = check_graph(&graph);
    let defining = checked
        .iter()
        .find(|module| {
            graph
                .module(module.module())
                .unwrap()
                .source()
                .display_path()
                == "@compiler.region"
        })
        .expect("the actual compiler service remains checked");
    let effects = defining
        .effects()
        .iter()
        .filter(|effect| effect.spelling == "DefaultAlloc")
        .collect::<Vec<_>>();
    let [allocation] = effects.as_slice() else {
        panic!("the defining service declares one DefaultAlloc");
    };
    assert_eq!(allocation.id.module(), defining.module());
    assert!(allocation.parameters.is_empty());
    let entry = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .unwrap();
    let operations = TraceOperations {
        allocation_effect: allocation.id,
        allocation: allocation
            .operations
            .iter()
            .map(|operation| operation.id)
            .collect(),
        source: entry
            .effects()
            .iter()
            .flat_map(|effect| effect.operations.iter().map(|operation| operation.id))
            .collect(),
    };
    let linked = link_modules(checked, graph.entry()).expect("fixture should link");
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
    (
        validate_effect_modules(unchecked, &sources, &module_sources)
            .expect("Core should validate"),
        operations,
    )
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

fn source_effect_trace(
    program: &ValidatedEffectProgram,
    operations: &TraceOperations,
    raw: &[EffectTraceEvent],
) -> Vec<EffectTraceEvent> {
    assert_eq!(
        operations.allocation.len(),
        2,
        "both canonical service operations are retained"
    );
    assert!(
        operations
            .allocation
            .iter()
            .all(|operation| !operations.source.contains(operation))
    );
    let mut handlers = HashMap::new();
    let mut pending = vec![program.root()];
    let mut visited = HashSet::new();
    while let Some(id) = pending.pop() {
        if !visited.insert(id) {
            continue;
        }
        let node = program.node(id).unwrap();
        if let EffectExprKind::Operation(EffectOperation::Handler(handler)) = &node.kind {
            let allocation = handler.effect().effect() == operations.allocation_effect;
            if allocation {
                assert!(handler.effect().arguments().is_empty());
            }
            let allowed = if allocation {
                &operations.allocation
            } else {
                &operations.source
            };
            assert!(
                allowed
                    .iter()
                    .any(|operation| operation.owner() == handler.effect().effect()),
                "unclassified handler instance {:?}",
                handler.effect()
            );
            let clauses = handler
                .clauses()
                .iter()
                .map(|clause| {
                    assert_eq!(clause.operation().owner(), handler.effect().effect());
                    assert!(allowed.contains(&clause.operation()));
                    clause.operation()
                })
                .collect::<Vec<_>>();
            assert!(
                handlers
                    .insert(
                        handler.id(),
                        (handler.effect().clone(), allocation, clauses)
                    )
                    .is_none(),
                "handler identity must be unique"
            );
        }
        pending.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
    }
    let handler_domain = |id: &HandlerId| {
        handlers
            .get(id)
            .unwrap_or_else(|| panic!("unclassified handler {id:?}"))
    };
    let operation_domain = |id: &OperationId| {
        if operations.allocation.contains(id) {
            true
        } else {
            assert!(
                operations.source.contains(id),
                "unclassified operation {id:?}"
            );
            false
        }
    };
    let mut source = Vec::new();
    let mut restoring = None;
    for event in raw {
        let preceding_resume = restoring.take();
        let allocation = match event {
            EffectTraceEvent::HandlerRestored(handler) => {
                let caused_by_allocation = preceding_resume
                    .expect("restoration must immediately follow Resume/restoration");
                restoring = Some(caused_by_allocation);
                let restored_is_allocation = handler_domain(handler).1;
                caused_by_allocation || restored_is_allocation
            }
            EffectTraceEvent::Resume(handler) => {
                let allocation = handler_domain(handler).1;
                restoring = Some(allocation);
                allocation
            }
            EffectTraceEvent::Request(operation) => operation_domain(operation),
            EffectTraceEvent::ClauseEntered(handler, operation) => {
                let (instance, allocation, clauses) = handler_domain(handler);
                assert_eq!(operation.owner(), instance.effect());
                assert!(
                    clauses.contains(operation),
                    "clause operation must belong to this exact handler"
                );
                assert_eq!(*allocation, operation_domain(operation));
                *allocation
            }
            EffectTraceEvent::HandlerActivated(handler)
            | EffectTraceEvent::HandlerSelected(handler)
            | EffectTraceEvent::ClauseReturned(handler)
            | EffectTraceEvent::Discard(handler) => handler_domain(handler).1,
            event => panic!("unexpected resource event in source handler fixture: {event:?}"),
        };
        if !allocation {
            source.push(*event);
        }
    }
    source
}

fn run_effect_source_with_trace(
    name: &str,
    source: &str,
) -> (ash::eval::Evaluation, Vec<EffectTraceEvent>) {
    let path = std::env::temp_dir().join(format!(
        "ash-effect-trace-{name}-{}-{}.ash",
        std::process::id(),
        SourceFile::new(name, "").unwrap().id().value()
    ));
    std::fs::write(&path, source).unwrap();
    let (program, operations) = effect_program_with_trace_operations(&path);
    let evaluation = evaluate_effect(&program).expect("effect Core should execute");
    let trace = source_effect_trace(&program, &operations, evaluation.effect_trace());
    std::fs::remove_file(path).unwrap();
    (evaluation, trace)
}

#[test]
fn newtype_pattern_branches_preserve_their_effectful_continuations() {
    for (name, branches) in [
        ("single", "Boxed((_, number)) => perform Ask.ask number\n"),
        (
            "fallback",
            "Boxed((true, number)) => perform Ask.ask number\nBoxed((_, number)) => perform Ask.ask number\n",
        ),
    ] {
        let source = format!(
            "newtype Boxed = Boxed((Bool, Int))\neffect Ask {{\nask : Int -> Int\n}}\nread : Boxed -> Int ! {{Ask}}\nread value = match value {{\n{branches}}}\nmain : Unit -> Int\nmain () = handle (read (Boxed((false, 40)))) with Ask {{\nask number => resume (number + 2)\n}}\n"
        );
        let evaluation = run_effect_source(name, &source);
        assert_eq!(evaluation.value.to_string(), "42");
    }
}

#[test]
fn generic_request_matches_its_concrete_caller_handler() {
    let evaluation = run_effect_source(
        "generic-helper",
        concat!(
            "effect E<T> {\nask : Unit -> Int\n}\n",
            "helper<T> : T -> Int ! {E<T>}\nhelper ignored = perform E<T>.ask ()\n",
            "main : Unit -> Int\nmain () = handle (helper 0) with E<Int> {\n",
            "ask ignored => resume 42\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
}

#[test]
fn generic_factory_closure_keeps_instantiation_after_return() {
    let evaluation = run_effect_source(
        "generic-factory",
        concat!(
            "effect E<T> {\nask : Unit -> Int\n}\n",
            "factory<T> : T -> (Unit -> Int ! {E<T>})\n",
            "factory ignored = fn(ignored) {\nperform E<T>.ask ()\n}\n",
            "main : Unit -> Int\nmain () = {\nlet request = factory 0\n",
            "handle (request ()) with E<Int> {\nask ignored => resume 42\n}\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
}

#[test]
fn generic_instances_and_returned_closures_keep_distinct_contexts() {
    let (evaluation, source_trace) = run_effect_source_with_trace(
        "generic-distinct",
        concat!(
            "effect E<T> {\nask : Unit -> Int\n}\n",
            "factory<T> : T -> (Unit -> Int ! {E<T>})\n",
            "factory ignored = fn(ignored) {\nperform E<T>.ask ()\n}\n",
            "main : Unit -> Int\nmain () = {\nlet first = factory 0\nlet second = factory true\n",
            "handle (handle (first () + second ()) with E<Bool> {\nask ignored => resume 2\n}) with E<Int> {\nask ignored => resume 40\n}\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
    let selected = source_trace
        .as_slice()
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::HandlerSelected(handler) => Some(handler),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(selected.len(), 2);
    assert_ne!(selected[0], selected[1]);
}

#[test]
fn generic_handler_uses_its_definition_context_after_capture_and_resume() {
    let (evaluation, source_trace) = run_effect_source_with_trace(
        "generic-handler",
        concat!(
            "effect E<T> {\nask : Unit -> Int\n}\n",
            "helper<T> : T -> Int ! {E<T>}\nhelper ignored = perform E<T>.ask ()\n",
            "run<T> : T -> Int\nrun value = handle (helper value + helper value) with E<T> {\nask ignored => resume 21\n}\n",
            "main : Unit -> Int\nmain () = run true\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
    assert_eq!(
        source_trace
            .as_slice()
            .iter()
            .filter(|event| matches!(event, EffectTraceEvent::HandlerRestored(_)))
            .count(),
        2
    );
}

#[test]
fn generic_higher_kinded_effect_argument_matches_exactly() {
    let evaluation = run_effect_source(
        "generic-higher-kind",
        concat!(
            "type Box<T> = Box(T)\neffect E<F : Type -> Type> {\nask : Unit -> Int\n}\n",
            "helper<F : Type -> Type> : F<Int> -> Int ! {E<F>}\nhelper ignored = perform E<F>.ask ()\n",
            "main : Unit -> Int\nmain () = handle (helper (Box(0))) with E<Box> {\nask ignored => resume 42\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
}

#[test]
fn generic_row_bearing_function_argument_preserves_complete_row_substitution() {
    let evaluation = run_effect_source(
        "generic-row-argument",
        concat!(
            "effect Ask {\nask : Unit -> Int\n}\neffect E<T> {\nask : Unit -> Int\n}\n",
            "helper<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {E<Unit -> Int ! {| R}>}\n",
            "helper ignored = perform E<Unit -> Int ! {| R}>.ask ()\n",
            "action : Unit -> Int ! {Ask}\naction () = perform Ask.ask ()\n",
            "main : Unit -> Int\nmain () = handle (helper action) with E<Unit -> Int ! {Ask}> {\nask ignored => resume 42\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
}

#[test]
fn polymorphic_row_value_specializes_in_a_local_annotation() {
    let evaluation = run_effect_source(
        "generic-row-local-value",
        concat!(
            "effect Ping<N> {\nping : Unit -> Unit\n}\n",
            "forward<N,A,E : EffectRow> : (Unit -> A ! {| E}) -> A ! {Ping<N> | E}\n",
            "forward cb = {\nlet ignored = perform Ping<N>.ping ()\ncb ()\n}\n",
            "main : Unit -> Int\nmain () = {\n",
            "let local : (Unit -> Int) -> Int ! {Ping<Int>} = forward\n",
            "handle (local (fn(ignored) {\n42\n})) with Ping<Int> {\nping ignored => resume ()\n}\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
}

#[test]
fn generic_row_forwarding_accepts_an_empty_effect_row() {
    let evaluation = run_effect_source(
        "generic-empty-row",
        concat!(
            "relay<R : EffectRow, T> : (Unit -> T ! {| R}) -> T ! {| R}\n",
            "relay f = f ()\n",
            "main : Unit -> Bool\nmain () = relay (fn(ignored) {\ntrue\n})\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "true");
}

#[test]
fn generic_method_row_forwarding_accepts_an_empty_effect_row() {
    let evaluation = run_effect_source(
        "generic-method-empty-row",
        concat!(
            "relay<R : EffectRow, T> : (Unit -> T ! {| R}) -> T ! {| R}\n",
            "relay f = f ()\n",
            "interface Read<A> {\nread<T> : (A, T) -> T\n}\n",
            "impl Read<Int> {\nread (ignored, extra) = relay (fn(ignored) {\nextra\n})\n}\n",
            "main : Unit -> Bool\nmain () = read (0, true)\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "true");
}

#[test]
fn generic_recursive_template_preserves_its_lexical_instantiation() {
    let evaluation = run_effect_source(
        "generic-recursive",
        concat!(
            "effect E<T> {\nask : Unit -> Int\n}\n",
            "helper<T> : (T, Int) -> Int ! {E<T>}\nhelper (value, count) = match count == 5 {\n",
            "true => perform E<T>.ask ()\nfalse => helper (value, count + 1)\n}\n",
            "main : Unit -> Int\nmain () = handle (helper (true, 0)) with E<Bool> {\nask ignored => resume 42\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
}

#[test]
fn generic_implementation_and_method_adapter_preserve_both_parameter_scopes() {
    let evaluation = run_effect_source(
        "generic-method-adapter",
        concat!(
            "type Box<T> = Box(T)\neffect E<T> {\nask : Unit -> Int\n}\n",
            "interface Read<A> {\nread<T> : (A, T) -> Int ! {E<T>}\n}\n",
            "helper<T> : T -> Int ! {E<T>}\nhelper ignored = perform E<T>.ask ()\n",
            "impl<A> Read<Box<A>> {\nread (value, extra) = helper extra\n}\n",
            "relay<A> : A -> Int ! {E<Bool>} where Read<A>\nrelay value = read (value, true)\n",
            "main : Unit -> Int\nmain () = handle (relay (Box(0))) with E<Bool> {\nask ignored => resume 42\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
}

#[test]
fn generic_method_with_nongeneric_implementation_matches_its_caller() {
    let evaluation = run_effect_source(
        "generic-simple-method",
        concat!(
            "effect E<T> {\nask : Unit -> Int\n}\n",
            "helper<T> : T -> Int ! {E<T>}\nhelper ignored = perform E<T>.ask ()\n",
            "interface Read<A> {\nread<T> : (A, T) -> Int ! {E<T>}\n}\n",
            "impl Read<Int> {\nread (value, extra) = helper extra\n}\n",
            "main : Unit -> Int\nmain () = handle (read (0, true)) with E<Bool> {\nask ignored => resume 42\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
}

#[test]
fn generic_implementation_with_monomorphic_method_matches_its_caller() {
    let evaluation = run_effect_source(
        "generic-simple-impl",
        concat!(
            "type Box<T> = Box(T)\neffect E<T> {\nask : Unit -> Int\n}\n",
            "helper<T> : T -> Int ! {E<T>}\nhelper ignored = perform E<T>.ask ()\n",
            "interface Read<A> {\nread : A -> Int ! {E<A>}\n}\n",
            "impl<A> Read<Box<A>> {\nread value = helper value\n}\n",
            "main : Unit -> Int\nmain () = handle (read (Box(0))) with E<Box<Int>> {\nask ignored => resume 42\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
}

#[test]
fn generic_request_operand_preserves_context_and_strict_effect_order() {
    let (evaluation, source_trace) = run_effect_source_with_trace(
        "generic-operand-order",
        concat!(
            "effect E<T> {\nask : Unit -> Int\n}\neffect Mark {\nmark : Unit -> Unit\n}\n",
            "helper<T> : T -> Int ! {E<T>, Mark}\nhelper ignored = perform E<T>.ask (perform Mark.mark ())\n",
            "main : Unit -> Int\nmain () = handle (handle (helper 0) with E<Int> {\nask ignored => resume 42\n}) with Mark {\nmark ignored => resume ()\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
    let trace = source_trace.as_slice();
    let [
        EffectTraceEvent::HandlerActivated(mark),
        EffectTraceEvent::HandlerActivated(ask),
        ..,
    ] = trace
    else {
        panic!("two handlers");
    };
    let selected = trace
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::HandlerSelected(handler) => Some(handler),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(selected, [mark, ask]);
}

#[test]
fn generic_instantiation_and_constructors_survive_both_core_transforms() {
    use ash::core::transform::{fold_effect_literal_primitives, identity_effect_traversal};
    let source = concat!(
        "type Option<T> =\nNone\n| Some(T)\neffect E<T> {\nask : Unit -> Int\n}\n",
        "factory<T> : T -> (Unit -> Int ! {E<T>})\nfactory ignored = fn(ignored) {\nperform E<T>.ask ()\n}\n",
        "main : Unit -> Int\nmain () = {\nlet unused : Option<Bool> = None\nlet f = factory (Some(0))\n",
        "handle (f ()) with E<Option<Int>> {\nask ignored => resume (40 + 2)\n}\n}\n",
    );
    let path = std::env::temp_dir().join(format!(
        "ash-instantiation-transforms-{}-{}.ash",
        std::process::id(),
        SourceFile::new("transform", "").unwrap().id().value()
    ));
    std::fs::write(&path, source).unwrap();
    let graph = load_module_graph(&path, &ModuleRoots::empty()).unwrap();
    let linked =
        validate_interface_evidence(link_modules(check_graph(&graph), graph.entry()).unwrap())
            .unwrap();
    let mut elaborator = EffectElaborator::for_module_program(&linked).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .unwrap();
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
    let mut program =
        validate_effect_modules(elaborator.finish(typed.node).unwrap(), &sources, &modules)
            .unwrap();
    let expected = evaluate_effect(&program).unwrap();
    for transform in [identity_effect_traversal, fold_effect_literal_primitives] {
        program =
            validate_effect_modules(transform(&program).unwrap(), &sources, &modules).unwrap();
        let actual = evaluate_effect(&program).unwrap();
        assert_eq!(actual.value.to_string(), "42");
        assert_eq!(actual.effect_trace(), expected.effect_trace());
    }
    std::fs::remove_file(path).unwrap();
}

#[test]
fn discard_abandons_suspended_addition_and_continues_the_clause() {
    let (evaluation, source_trace) = run_effect_source_with_trace(
        "discard-addition",
        concat!(
            "effect Ask {\nask : Unit -> Int\n}\n\n",
            "main : Unit -> Int\n",
            "main () = handle (perform Ask.ask () + 100) with Ask {\n",
            "ask ignored => {\nlet () = discard\n40 + 2\n}\n}\n",
        ),
    );
    assert_eq!(evaluation.value.to_string(), "42");
    assert!(matches!(source_trace.as_slice(), [
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
    let (evaluation, source_trace) = run_effect_source_with_trace(
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
    assert!(matches!(source_trace.as_slice(), [
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
    let (evaluation, source_trace) = run_effect_source_with_trace(
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
    let completion = source_trace
        .as_slice()
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
    let (evaluation, source_trace) = run_effect_source_with_trace(
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
    let returned = source_trace
        .as_slice()
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::ClauseReturned(handler) => Some(*handler),
            _ => None,
        })
        .collect::<Vec<_>>();
    let discarded = source_trace
        .as_slice()
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
        let (evaluation, source_trace) = run_effect_source_with_trace("mixed-completion", &source);
        assert_eq!(evaluation.value.to_string(), expected);
        assert_eq!(
            source_trace
                .as_slice()
                .iter()
                .filter(|event| matches!(event, EffectTraceEvent::Resume(_)))
                .count(),
            resumes
        );
    }
}

#[test]
fn handled_request_preserves_erased_newtype_values_across_resume() {
    let (evaluation, source_trace) = run_effect_source_with_trace(
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
        source_trace.as_slice(),
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
    let (program, operations) = effect_program_with_trace_operations(&path);
    let evaluation = evaluate_effect(&program).expect("validated Core should execute");
    let source_trace = source_effect_trace(&program, &operations, evaluation.effect_trace());
    let _ = std::fs::remove_file(path);
    assert_eq!(evaluation.value.to_string(), "112");
    let boundaries = source_trace.as_slice();
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
fn tail_and_strict_resumes_keep_later_effect_and_clause_order() {
    for (clause, expected) in [
        ("resume 41", "42"),
        ("{\nlet continued = resume 41\ncontinued + 1\n}", "43"),
        ("1 + (resume 41)", "43"),
    ] {
        let source = format!(
            "effect Ask {{\nask : Unit -> Int\n}}\n\
             effect Mark {{\nmark : Int -> Int\n}}\n\
             main : Unit -> Int\nmain () = handle (\n\
             handle ({{\nlet value = perform Ask.ask ()\nperform Mark.mark value\n}}) with Ask {{\n\
             ask ignored => {clause}\n}}\n) with Mark {{\nmark value => resume (value + 1)\n}}\n"
        );
        let (evaluation, trace) = run_effect_source_with_trace("strict-resume", &source);
        assert_eq!(evaluation.value.to_string(), expected);
        let [
            EffectTraceEvent::HandlerActivated(outer),
            EffectTraceEvent::HandlerActivated(inner),
            ..,
        ] = trace.as_slice()
        else {
            panic!("handler activation order: {trace:?}");
        };
        let significant = trace
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    EffectTraceEvent::Request(_)
                        | EffectTraceEvent::Resume(_)
                        | EffectTraceEvent::ClauseReturned(_)
                )
            })
            .copied()
            .collect::<Vec<_>>();
        assert!(
            matches!(significant.as_slice(), [
            EffectTraceEvent::Request(_), EffectTraceEvent::Resume(resumed_inner),
            EffectTraceEvent::Request(_), EffectTraceEvent::Resume(resumed_outer),
            EffectTraceEvent::ClauseReturned(returned_inner), EffectTraceEvent::ClauseReturned(returned_outer),
        ] if resumed_inner == inner && returned_inner == inner && resumed_outer == outer && returned_outer == outer),
            "source effects and deferred returns: {significant:?}"
        );
    }
}

#[test]
fn nearest_delegation_and_sequential_requests_preserve_clause_control() {
    let (evaluation, source_trace) = run_effect_source_with_trace(
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
    let selected = source_trace
        .as_slice()
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
    let (evaluation, source_trace) = run_effect_source_with_trace(
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
    let selected = source_trace
        .as_slice()
        .iter()
        .filter(|event| matches!(event, EffectTraceEvent::HandlerSelected(_)))
        .count();
    assert_eq!(selected, 2);
}

#[test]
fn clause_request_bypasses_captured_intervening_handler() {
    let (evaluation, source_trace) = run_effect_source_with_trace(
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
    let selected = source_trace
        .as_slice()
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
            let entry = checked
                .iter()
                .find(|module| module.module() == graph.entry())
                .expect("the actual entry remains checked");
            let registry = entry.registry().clone();
            let ask = entry
                .effects()
                .iter()
                .find(|effect| effect.spelling == "Ask")
                .expect("the entry declares Ask");
            let mark = entry
                .effects()
                .iter()
                .find(|effect| effect.spelling == "Mark")
                .expect("the entry declares Mark");
            assert_eq!(ask.id.module(), graph.entry());
            assert_eq!(mark.id.module(), graph.entry());
            let ask_instance = EffectInstance::new(ask.id, Box::new([]));
            let mark_instance = EffectInstance::new(mark.id, Box::new([]));
            let origin = Origin::Source(
                graph
                    .module(graph.entry())
                    .unwrap()
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
            let sources = graph
                .modules()
                .iter()
                .map(|module| module.source())
                .collect::<Vec<_>>();
            let relation = graph
                .modules()
                .iter()
                .map(|module| (module.id(), module.source().id()))
                .collect::<Vec<_>>();
            let program = validate_effect_modules(
                builder.finish(root).expect("Core should finish"),
                &sources,
                &relation,
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
