use std::{
    collections::HashMap,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{
        CoreBuilder, NodeId, Primitive, PureComputation, PureExprKind, PureValue,
        transform::{fold_literal_primitives, identity_traversal},
        validate, validate_modules,
    },
    driver::{Observation, RunConfiguration, run_path},
    elaborate::{Elaborator, check_module, link_modules},
    eval::{TraceEvent, evaluate},
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    render,
    resolve::{DependencyExports, resolve_module},
    resolved::{
        CheckedModule, ResolvedApplicationExpr, ResolvedExpr, ResolvedExprKind, ResolvedOccurrence,
    },
    source::{GeneratedReason, Origin, SourceFile},
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempFile(PathBuf);

impl TempFile {
    fn write(text: &str) -> Self {
        let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ash-semantics-{}-{id}.ash", std::process::id()));
        fs::write(&path, text).expect("test module should be writable");
        Self(path)
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

struct ModuleFixture {
    file: TempFile,
    graph: ModuleGraph,
}

impl ModuleFixture {
    fn load(text: &str) -> Self {
        let file = TempFile::write(text);
        let graph = load_module_graph(&file.0, &ModuleRoots::empty())
            .expect("single-module fixture should load");
        Self { file, graph }
    }

    fn run(&self) -> Observation {
        run_path(RunConfiguration {
            entry: self.file.0.clone(),
            roots: ModuleRoots::empty(),
        })
        .expect("module should run")
    }

    fn sources(&self) -> Vec<&SourceFile> {
        self.graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect()
    }

    fn module_sources(&self) -> Vec<(ash::module::ModuleId, ash::source::SourceId)> {
        self.graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect()
    }
}

struct ElaboratedModule {
    fixture: ModuleFixture,
    program: ash::core::ValidatedProgram,
}

impl ElaboratedModule {
    fn revalidate(&self, program: ash::core::UnvalidatedProgram) -> ash::core::ValidatedProgram {
        let sources = self.fixture.sources();
        let module_sources = self.fixture.module_sources();
        validate_modules(program, &sources, &module_sources)
            .expect("transformed module Core should validate independently")
    }
}

fn assert_exact_core(
    before: &ash::core::ValidatedProgram,
    after: &ash::core::ValidatedProgram,
) -> HashMap<NodeId, NodeId> {
    let mut forward = HashMap::new();
    let mut reverse = HashMap::new();
    let mut work = vec![(before.root(), after.root())];
    while let Some((before_id, after_id)) = work.pop() {
        if let Some(previous) = forward.insert(before_id, after_id) {
            assert_eq!(previous, after_id, "identity changed graph sharing");
            continue;
        }
        assert!(reverse.insert(after_id, before_id).is_none());
        let before_node = before.node(before_id).expect("validated node");
        let after_node = after.node(after_id).expect("validated node");
        assert_eq!(after_node.ty, before_node.ty);
        assert_eq!(after_node.origin, before_node.origin);
        match (&before_node.kind, &after_node.kind) {
            (
                PureExprKind::Value(PureValue::Integer(before)),
                PureExprKind::Value(PureValue::Integer(after)),
            ) => assert_eq!(after.value(), before.value()),
            (
                PureExprKind::Value(PureValue::Boolean(before)),
                PureExprKind::Value(PureValue::Boolean(after)),
            ) => assert_eq!(after.value(), before.value()),
            (PureExprKind::Value(PureValue::Unit(_)), PureExprKind::Value(PureValue::Unit(_))) => {}
            (
                PureExprKind::Value(PureValue::Function(before)),
                PureExprKind::Value(PureValue::Function(after)),
            ) => {
                assert_eq!(after.parameter().id(), before.parameter().id());
                assert_eq!(after.parameter().ty(), before.parameter().ty());
                assert_eq!(after.parameter().origin(), before.parameter().origin());
                work.push((before.body(), after.body()));
            }
            (PureExprKind::Variable(before), PureExprKind::Variable(after)) => {
                assert_eq!(after.binder(), before.binder());
            }
            (
                PureExprKind::Computation(PureComputation::Bind(before)),
                PureExprKind::Computation(PureComputation::Bind(after)),
            ) => {
                assert_eq!(after.binder().id(), before.binder().id());
                assert_eq!(after.binder().ty(), before.binder().ty());
                assert_eq!(after.binder().origin(), before.binder().origin());
                work.push((before.body(), after.body()));
                work.push((before.initializer(), after.initializer()));
            }
            (
                PureExprKind::Computation(PureComputation::RecursiveBind(before)),
                PureExprKind::Computation(PureComputation::RecursiveBind(after)),
            ) => {
                assert_eq!(after.members().len(), before.members().len());
                for (before_member, after_member) in before.members().iter().zip(after.members()) {
                    assert_eq!(after_member.binder().id(), before_member.binder().id());
                    assert_eq!(after_member.binder().ty(), before_member.binder().ty());
                    assert_eq!(
                        after_member.binder().origin(),
                        before_member.binder().origin()
                    );
                    work.push((before_member.initializer(), after_member.initializer()));
                }
                work.push((before.body(), after.body()));
            }
            (
                PureExprKind::Computation(PureComputation::Apply(before)),
                PureExprKind::Computation(PureComputation::Apply(after)),
            ) => {
                work.push((before.argument(), after.argument()));
                work.push((before.function(), after.function()));
            }
            (
                PureExprKind::Computation(PureComputation::Primitive(before)),
                PureExprKind::Computation(PureComputation::Primitive(after)),
            ) => {
                assert_eq!(after.primitive(), before.primitive());
                work.push((before.right(), after.right()));
                work.push((before.left(), after.left()));
            }
            (
                PureExprKind::Computation(PureComputation::Match(before)),
                PureExprKind::Computation(PureComputation::Match(after)),
            ) => {
                assert_eq!(after.arms().len(), before.arms().len());
                for (before_arm, after_arm) in before.arms().iter().zip(after.arms()) {
                    assert_eq!(after_arm.pattern(), before_arm.pattern());
                    assert_eq!(after_arm.origin(), before_arm.origin());
                    work.push((before_arm.body(), after_arm.body()));
                }
                work.push((before.scrutinee(), after.scrutinee()));
            }
            _ => panic!("identity changed a closed Core feature"),
        }
    }
    assert_eq!(forward.len(), before.node_count());
    assert_eq!(reverse.len(), after.node_count());
    forward
}

fn check_graph(graph: &ModuleGraph) -> Vec<CheckedModule> {
    let mut checked = Vec::<CheckedModule>::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency| dependency.module() == edge.target())
                    .expect("dependency order should publish the target first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("checked summary should authenticate its edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies).expect("module should resolve");
        drop(dependencies);
        checked.push(check_module(resolved).expect("module should check"));
    }
    checked
}

fn elaborated(text: &str) -> ElaboratedModule {
    let fixture = ModuleFixture::load(text);
    let checked = check_graph(&fixture.graph);
    let entry = checked
        .iter()
        .find(|module| module.module() == fixture.graph.entry())
        .expect("checked graph should retain its entry");
    let main = entry
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "main")
        .expect("entry should declare main");
    let span = main.origin.primary_span();
    let result = ResolvedExpr {
        kind: ResolvedExprKind::Apply(ResolvedApplicationExpr {
            function: Box::new(ResolvedExpr {
                kind: ResolvedExprKind::Occurrence(ResolvedOccurrence {
                    binder: main.binder,
                    spelling: "main".to_owned(),
                    origin: main.origin.clone(),
                }),
                span,
            }),
            argument: Box::new(ResolvedExpr {
                kind: ResolvedExprKind::Unit,
                span,
            }),
        }),
        span,
    };
    let linked = link_modules(checked, fixture.graph.entry(), result)
        .expect("checked module graph should link");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("binder namespace should fit Core");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("test module should elaborate");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("elaborated root should finish");
    let sources = fixture.sources();
    let module_sources = fixture.module_sources();
    let program = validate_modules(unchecked, &sources, &module_sources)
        .expect("elaborated module Core should validate");
    ElaboratedModule { fixture, program }
}

fn linked_main_body(program: &ash::core::ValidatedProgram) -> NodeId {
    let root = program.node(program.root()).expect("linked module root");
    let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &root.kind else {
        panic!("expected one linked module group");
    };
    let main = program
        .node(
            group
                .members()
                .last()
                .expect("module should contain main")
                .initializer(),
        )
        .expect("main initializer");
    let PureExprKind::Value(PureValue::Function(main)) = &main.kind else {
        panic!("main should lower to a function");
    };
    let body = program.node(main.body()).expect("main function body");
    let PureExprKind::Computation(PureComputation::Match(body)) = &body.kind else {
        panic!("equational main should lower its Unit pattern to a match");
    };
    assert_eq!(body.arms().len(), 1);
    body.arms()[0].body()
}

fn recursive_machine_core() -> (SourceFile, ash::core::ValidatedProgram) {
    let source =
        SourceFile::new("recursive-machine.ash", "recursive core").expect("test source should fit");
    let span = source
        .span(ash::source::ByteRange::new(0, 14).expect("ordered range"))
        .expect("source span");
    let origin = Origin::Source(span);
    let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
    let mut builder = CoreBuilder::new();
    let first = builder
        .binder(function_type.clone(), origin.clone())
        .expect("first binder");
    let second = builder
        .binder(function_type.clone(), origin.clone())
        .expect("second binder");
    let first_parameter = builder
        .binder(Type::Unit, origin.clone())
        .expect("first parameter");
    let second_use = builder
        .variable(second.id(), function_type.clone(), origin.clone())
        .expect("second occurrence");
    let first_argument = builder
        .unit(Type::Unit, origin.clone())
        .expect("first argument");
    let first_body = builder
        .application(second_use, first_argument, Type::Int, origin.clone())
        .expect("first body");
    let first_function = builder
        .function(
            first_parameter,
            first_body,
            function_type.clone(),
            origin.clone(),
        )
        .expect("first function");
    let second_parameter = builder
        .binder(Type::Unit, origin.clone())
        .expect("second parameter");
    let first_use = builder
        .variable(first.id(), function_type.clone(), origin.clone())
        .expect("first occurrence");
    let forty_two = builder
        .integer(
            ash::integer::Integer::parse_decimal("42").expect("valid integer"),
            Type::Int,
            origin.clone(),
        )
        .expect("second result");
    let retained_first = builder
        .binder(function_type.clone(), origin.clone())
        .expect("retained alias");
    let second_body = builder
        .binding(
            retained_first,
            first_use,
            forty_two,
            Type::Int,
            origin.clone(),
        )
        .expect("second body");
    let second_function = builder
        .function(
            second_parameter,
            second_body,
            function_type.clone(),
            origin.clone(),
        )
        .expect("second function");
    let entry = builder
        .variable(first.id(), function_type, origin.clone())
        .expect("entry occurrence");
    let entry_argument = builder
        .unit(Type::Unit, origin.clone())
        .expect("entry argument");
    let result = builder
        .application(entry, entry_argument, Type::Int, origin.clone())
        .expect("entry application");
    let root = builder
        .recursive_binding(
            vec![(first, first_function), (second, second_function)],
            result,
            Type::Int,
            origin,
        )
        .expect("recursive group");
    let validated = validate(builder.finish(root).expect("root"), &[&source])
        .expect("recursive machine Core should validate");
    (source, validated)
}

#[test]
fn recursive_machine_evaluates_mutual_function_templates() {
    let (_source, program) = recursive_machine_core();

    let evaluation = evaluate(&program).expect("recursive group should evaluate");

    assert_eq!(evaluation.value.to_string(), "42");
}

#[test]
fn recursive_machine_evaluates_a_self_reference() {
    let module = elaborated(concat!(
        "main : Unit -> Int\n",
        "main () = {\n",
        "let rec self : Unit -> Int = fn(ignored) {\n",
        "let retain : Unit -> Int = self\n",
        "42\n",
        "}\n",
        "self ()\n",
        "}\n",
    ));

    let evaluation = evaluate(&module.program).expect("recursive self lookup should evaluate");

    assert_eq!(evaluation.value.to_string(), "42");
}

#[test]
fn identity_traversal_preserves_recursive_groups() {
    let (source, before) = recursive_machine_core();

    let after = validate(
        identity_traversal(&before).expect("recursive Core should traverse"),
        &[&source],
    )
    .expect("rebuilt recursive Core should validate");

    let remapped = assert_exact_core(&before, &after);
    assert_eq!(remapped.len(), before.node_count());
    assert_eq!(
        evaluate(&after)
            .expect("rebuilt Core should run")
            .value
            .to_string(),
        "42"
    );
}

#[test]
fn recursive_group_survives_literal_folding_and_independent_validation() {
    let before = elaborated(concat!(
        "main : Unit -> Int\n",
        "main () = {\n",
        "let rec answer : Unit -> Int = fn(ignored) {\n",
        "20 + 22\n",
        "}\n",
        "answer ()\n",
        "}\n",
    ));
    let after = before.revalidate(
        fold_literal_primitives(&before.program).expect("recursive Core should transform"),
    );

    let root = after
        .node(linked_main_body(&after))
        .expect("local recursive root");
    assert!(matches!(
        root.kind,
        PureExprKind::Computation(PureComputation::RecursiveBind(_))
    ));
    assert!(after.node_count() < before.program.node_count());
    assert_eq!(
        evaluate(&after)
            .expect("folded recursive Core should evaluate")
            .value
            .to_string(),
        "42"
    );
}

#[test]
fn arbitrary_precision_observations_and_traces_exceed_unsigned_machine_width() {
    const BIG: &str = "340282366920938463463374607431768211456";
    const DOUBLE: &str = "680564733841876926926749214863536422912";
    const NEXT: &str = "340282366920938463463374607431768211457";
    const SQUARE: &str =
        "115792089237316195423570985008687907853269984665640564039457584007913129639936";
    for (name, text, expected_value, expected_type, expected_trace_len) in [
        (
            "literal",
            format!("main : Unit -> Int\nmain () = {BIG}\n"),
            BIG,
            "Int",
            7,
        ),
        (
            "sum",
            format!("main : Unit -> Int\nmain () = {BIG} + {BIG}\n"),
            DOUBLE,
            "Int",
            9,
        ),
        (
            "product",
            format!("main : Unit -> Int\nmain () = {BIG} * {BIG}\n"),
            SQUARE,
            "Int",
            9,
        ),
        (
            "equality",
            format!("main : Unit -> Bool\nmain () = {BIG} == {BIG}\n"),
            "true",
            "Bool",
            9,
        ),
        (
            "inequality",
            format!("main : Unit -> Bool\nmain () = {BIG} == {NEXT}\n"),
            "false",
            "Bool",
            9,
        ),
    ] {
        let fixture = ModuleFixture::load(&text);
        let observation = fixture.run();
        assert_eq!(observation.value.to_string(), expected_value, "{name}");
        assert_eq!(observation.ty.to_string(), expected_type, "{name}");
        assert_eq!(
            render::observation(&observation),
            format!("{expected_value} : {expected_type}\n"),
            "{name}"
        );

        let module = elaborated(&text);
        let program = &module.program;
        let evaluation = evaluate(program).expect("validated Core should evaluate");
        assert_eq!(evaluation.value.to_string(), expected_value, "{name}");
        assert_eq!(evaluation.trace.len(), expected_trace_len, "{name}");
        let traced_integer_values = evaluation
            .trace
            .iter()
            .filter_map(|event| match event {
                TraceEvent::Enter(node) => program.node(*node),
            })
            .filter_map(|expression| match &expression.kind {
                PureExprKind::Value(PureValue::Integer(integer)) => {
                    Some(integer.value().to_string())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(
            traced_integer_values.iter().any(|value| value == BIG),
            "{name}"
        );
    }
}

#[test]
fn literal_addition_folds_with_exact_type_and_causal_generated_origin() {
    let before = elaborated("main : Unit -> Int\nmain () = 20 + 22\n");
    let operation_origin = before
        .program
        .node(linked_main_body(&before.program))
        .expect("validated root")
        .origin
        .clone();

    let after = before.revalidate(
        fold_literal_primitives(&before.program).expect("validated Core should transform"),
    );

    let root = after
        .node(linked_main_body(&after))
        .expect("validated root");
    assert_eq!(root.ty, ash::types::Type::Int);
    let Origin::Generated { cause, reason } = &root.origin else {
        panic!("folded literal should have a generated origin")
    };
    assert_eq!(reason, &GeneratedReason::ConstantFolding);
    assert_eq!(reason.to_string(), "constant folding");
    assert_eq!(cause.as_ref(), &operation_origin);
    let PureExprKind::Value(PureValue::Integer(value)) = &root.kind else {
        panic!("literal addition should fold to an integer")
    };
    assert_eq!(value.value().to_string(), "42");

    let before_evaluation = evaluate(&before.program).expect("validated input should evaluate");
    let after_evaluation = evaluate(&after).expect("validated transform should evaluate");
    assert_eq!(
        after_evaluation.value.to_string(),
        before_evaluation.value.to_string()
    );
    // Folding removes the operation and operand entries while preserving the
    // linked main call and final observation. Trace node identities are local.
    assert_eq!(before_evaluation.trace.len(), 9);
    assert_eq!(after_evaluation.trace.len(), 7);
}

#[test]
fn generated_provenance_reasons_have_stable_plain_names() {
    assert_eq!(
        [
            GeneratedReason::FunctionLowering,
            GeneratedReason::BindingLowering,
            GeneratedReason::TypeChecking,
            GeneratedReason::ConstantFolding,
        ]
        .map(|reason| reason.to_string()),
        [
            "function lowering",
            "binding lowering",
            "type checking",
            "constant folding",
        ]
    );
}

#[test]
fn literal_multiplication_folds_but_integer_equality_remains_a_primitive() {
    let multiplication = elaborated("main : Unit -> Int\nmain () = 6 * 7\n");
    let folded = multiplication.revalidate(
        fold_literal_primitives(&multiplication.program).expect("validated Core should transform"),
    );
    let PureExprKind::Value(PureValue::Integer(value)) = &folded
        .node(linked_main_body(&folded))
        .expect("validated root")
        .kind
    else {
        panic!("literal multiplication should fold")
    };
    assert_eq!(value.value().to_string(), "42");

    let equality = elaborated("main : Unit -> Bool\nmain () = 42 == 42\n");
    let unchanged = equality.revalidate(
        fold_literal_primitives(&equality.program).expect("validated Core should transform"),
    );
    assert!(matches!(
        unchanged
            .node(linked_main_body(&unchanged))
            .expect("validated root")
            .kind,
        PureExprKind::Computation(PureComputation::Primitive(_))
    ));
}

#[test]
fn identity_traversal_preserves_exact_types_origins_and_primitive_structure() {
    let before = elaborated("main : Unit -> Int\nmain () = 1 + 2\n");

    let after = before
        .revalidate(identity_traversal(&before.program).expect("validated Core should traverse"));

    let before_root = before
        .program
        .node(linked_main_body(&before.program))
        .expect("validated root");
    let after_root = after
        .node(linked_main_body(&after))
        .expect("validated root");
    assert_eq!(after_root.ty, before_root.ty);
    assert_eq!(after_root.origin, before_root.origin);

    let PureExprKind::Computation(PureComputation::Primitive(before_operation)) = &before_root.kind
    else {
        panic!("expected primitive root")
    };
    let PureExprKind::Computation(PureComputation::Primitive(after_operation)) = &after_root.kind
    else {
        panic!("expected primitive root")
    };
    assert_eq!(after_operation.primitive(), before_operation.primitive());

    for (before_child, after_child) in [
        (before_operation.left(), after_operation.left()),
        (before_operation.right(), after_operation.right()),
    ] {
        let before_child = before.program.node(before_child).expect("validated child");
        let after_child = after.node(after_child).expect("validated child");
        assert_eq!(after_child.ty, before_child.ty);
        assert_eq!(after_child.origin, before_child.origin);
        assert!(matches!(
            (&before_child.kind, &after_child.kind),
            (
                PureExprKind::Value(PureValue::Integer(_)),
                PureExprKind::Value(PureValue::Integer(_))
            )
        ));
    }

    let before_evaluation = evaluate(&before.program).expect("validated input should evaluate");
    let after_evaluation = evaluate(&after).expect("validated identity should evaluate");
    assert_eq!(
        after_evaluation.value.to_string(),
        before_evaluation.value.to_string()
    );
    assert_eq!(after_evaluation.trace.len(), before_evaluation.trace.len());
}

#[test]
fn identity_traversal_preserves_shared_core_edges() {
    let source = SourceFile::new("shared-identity.ash", "1").expect("test source should fit");
    let span = source
        .span(ash::source::ByteRange::new(0, 1).expect("ordered range"))
        .expect("test span should fit");
    let origin = Origin::Source(span);
    let mut builder = CoreBuilder::new();
    let shared = builder
        .integer(
            ash::integer::Integer::parse_decimal("1").expect("valid integer"),
            Type::Int,
            origin.clone(),
        )
        .expect("small Core should fit");
    let root = builder
        .primitive(Primitive::Add, shared, shared, Type::Int, origin)
        .expect("small Core should fit");
    let before = validate(
        builder.finish(root).expect("root should finish"),
        &[&source],
    )
    .expect("shared Core should validate");
    let after = validate(
        identity_traversal(&before).expect("validated Core should traverse"),
        &[&source],
    )
    .expect("identity output should validate");
    let remapped = assert_exact_core(&before, &after);
    assert_eq!(remapped.len(), 2);
}

#[test]
fn identity_traversal_preserves_every_core_feature_and_trace_relation() {
    let before = elaborated(include_str!("fixtures/first-stratum/valid/v008-mixed.ash"));
    let after = before
        .revalidate(identity_traversal(&before.program).expect("validated Core should traverse"));
    let remapped = assert_exact_core(&before.program, &after);

    let before_evaluation = evaluate(&before.program).expect("validated input should evaluate");
    let after_evaluation = evaluate(&after).expect("validated identity should evaluate");
    assert_eq!(
        after_evaluation.value.to_string(),
        before_evaluation.value.to_string()
    );
    assert_eq!(after_evaluation.trace.len(), before_evaluation.trace.len());
    for (before_event, after_event) in before_evaluation.trace.iter().zip(&after_evaluation.trace) {
        let (TraceEvent::Enter(before_node), TraceEvent::Enter(after_node)) =
            (before_event, after_event);
        assert_eq!(remapped.get(before_node), Some(after_node));
    }

    for text in [
        "main : Unit -> Bool\nmain () = true\n",
        "main : Unit -> Unit\nmain () = ()\n",
        "main : Unit -> Bool\nmain () = 1 == 1\n",
    ] {
        let before = elaborated(text);
        let after = before.revalidate(
            identity_traversal(&before.program).expect("validated Core should traverse"),
        );
        let _ = assert_exact_core(&before.program, &after);
    }
}

#[test]
fn ten_thousand_nested_additions_grow_explicit_frames_on_a_small_host_stack() {
    const ADDITIONS: usize = 10_000;
    let thread = std::thread::Builder::new()
        .name("deep-machine".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let source = SourceFile::new("deep-core.ash", "0").expect("test source should fit");
            let span = source
                .span(ash::source::ByteRange::new(0, 1).expect("ordered range"))
                .expect("test span should fit");
            let origin = Origin::Source(span);
            let mut builder = CoreBuilder::new();
            let mut root = builder
                .integer(
                    ash::integer::Integer::parse_decimal("0").expect("valid integer"),
                    Type::Int,
                    origin.clone(),
                )
                .expect("deep arena should fit");
            for _ in 0..ADDITIONS {
                let one = builder
                    .integer(
                        ash::integer::Integer::parse_decimal("1").expect("valid integer"),
                        Type::Int,
                        origin.clone(),
                    )
                    .expect("deep arena should fit");
                root = builder
                    .primitive(Primitive::Add, root, one, Type::Int, origin.clone())
                    .expect("deep arena should fit");
            }
            let program = validate(
                builder.finish(root).expect("root should finish"),
                &[&source],
            )
            .expect("deep Core should validate");
            let traversed = validate(
                identity_traversal(&program).expect("deep validated Core should traverse"),
                &[&source],
            )
            .expect("deep identity output should validate");
            assert_eq!(traversed.node_count(), program.node_count());
            drop(program);
            let evaluation = evaluate(&traversed).expect("deep validated Core should evaluate");
            (
                evaluation.value.to_string(),
                evaluation.trace.len(),
                evaluation.max_frame_depth,
            )
        })
        .expect("small-stack thread should start");

    let (value, trace_len, max_frame_depth) = thread
        .join()
        .expect("machine should not use source-proportional Rust stack");
    assert_eq!(value, ADDITIONS.to_string());
    assert_eq!(trace_len, ADDITIONS * 2 + 1);
    assert_eq!(max_frame_depth, ADDITIONS);
}
