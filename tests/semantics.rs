use std::collections::HashMap;

use ash::{
    core::{
        CoreBuilder, NodeId, Primitive, PureComputation, PureExprKind, PureValue,
        transform::{fold_literal_primitives, identity_traversal},
        validate,
    },
    driver::run_source,
    elaborate::Elaborator,
    eval::{TraceEvent, evaluate},
    lexer::lex,
    parser::{parse, project},
    render,
    resolve::resolve,
    source::{GeneratedReason, Origin, SourceFile},
    types::Type,
};

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
            _ => panic!("identity changed a closed Core feature"),
        }
    }
    assert_eq!(forward.len(), before.node_count());
    assert_eq!(reverse.len(), after.node_count());
    forward
}

fn elaborated(source: &SourceFile) -> ash::core::ValidatedProgram {
    let lexed = lex(source).expect("test source should lex");
    assert!(lexed.diagnostics.is_empty());
    let tree = parse(lexed);
    assert!(tree.parse_diagnostics().is_empty());
    let surface = project(source, &tree).expect("test source should project");
    let resolved = resolve(&surface).expect("test source should resolve");
    let mut elaborator =
        Elaborator::for_program(&resolved).expect("binder namespace should fit Core");
    let typed = elaborator
        .synthesize_program(&resolved)
        .expect("test source should elaborate");
    validate(
        elaborator
            .finish(typed.node)
            .expect("elaborated root should finish"),
        &[source],
    )
    .expect("elaborated Core should validate")
}

#[test]
fn arbitrary_precision_observations_and_traces_exceed_unsigned_machine_width() {
    const BIG: &str = "340282366920938463463374607431768211456";
    const DOUBLE: &str = "680564733841876926926749214863536422912";
    const NEXT: &str = "340282366920938463463374607431768211457";
    const SQUARE: &str =
        "115792089237316195423570985008687907853269984665640564039457584007913129639936";
    for (name, text, expected_value, expected_type, expected_trace_len) in [
        ("literal", format!("{BIG}\n"), BIG, "Int", 1),
        ("sum", format!("{BIG} + {BIG}\n"), DOUBLE, "Int", 3),
        ("product", format!("{BIG} * {BIG}\n"), SQUARE, "Int", 3),
        ("equality", format!("{BIG} == {BIG}\n"), "true", "Bool", 3),
        (
            "inequality",
            format!("{BIG} == {NEXT}\n"),
            "false",
            "Bool",
            3,
        ),
    ] {
        let observation = run_source(
            SourceFile::new(format!("{name}-output.ash"), text.clone())
                .expect("test source should fit"),
        )
        .expect("arbitrary-precision program should run");
        assert_eq!(observation.value.to_string(), expected_value);
        assert_eq!(observation.ty.to_string(), expected_type);
        assert_eq!(
            render::observation(&observation),
            format!("{expected_value} : {expected_type}\n")
        );

        let source =
            SourceFile::new(format!("{name}-trace.ash"), text).expect("test source should fit");
        let program = elaborated(&source);
        let evaluation = evaluate(&program).expect("validated Core should evaluate");
        assert_eq!(evaluation.value.to_string(), expected_value);
        assert_eq!(evaluation.trace.len(), expected_trace_len);
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
        assert!(traced_integer_values.iter().any(|value| value == BIG));
    }
}

#[test]
fn literal_addition_folds_with_exact_type_and_causal_generated_origin() {
    let source = SourceFile::new("fold.ash", "20 + 22\n").expect("test source should fit");
    let before = elaborated(&source);
    let operation_origin = before
        .node(before.root())
        .expect("validated root")
        .origin
        .clone();

    let after = validate(
        fold_literal_primitives(&before).expect("validated Core should transform"),
        &[&source],
    )
    .expect("folded output should independently validate");

    let root = after.node(after.root()).expect("validated root");
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

    let before_evaluation = evaluate(&before).expect("validated input should evaluate");
    let after_evaluation = evaluate(&after).expect("validated transform should evaluate");
    assert_eq!(
        after_evaluation.value.to_string(),
        before_evaluation.value.to_string()
    );
    // Folding removes the operation and operand entries while preserving the
    // final observation. Trace node identities are implementation-local.
    assert_eq!(before_evaluation.trace.len(), 3);
    assert_eq!(after_evaluation.trace.len(), 1);
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
    let multiplication_source =
        SourceFile::new("multiply.ash", "6 * 7\n").expect("test source should fit");
    let multiplication = elaborated(&multiplication_source);
    let folded = validate(
        fold_literal_primitives(&multiplication).expect("validated Core should transform"),
        &[&multiplication_source],
    )
    .expect("folded output should validate");
    let PureExprKind::Value(PureValue::Integer(value)) =
        &folded.node(folded.root()).expect("validated root").kind
    else {
        panic!("literal multiplication should fold")
    };
    assert_eq!(value.value().to_string(), "42");

    let equality_source =
        SourceFile::new("equal.ash", "42 == 42\n").expect("test source should fit");
    let equality = elaborated(&equality_source);
    let unchanged = validate(
        fold_literal_primitives(&equality).expect("validated Core should transform"),
        &[&equality_source],
    )
    .expect("non-folded output should validate");
    assert!(matches!(
        unchanged
            .node(unchanged.root())
            .expect("validated root")
            .kind,
        PureExprKind::Computation(PureComputation::Primitive(_))
    ));
}

#[test]
fn identity_traversal_preserves_exact_types_origins_and_primitive_structure() {
    let source = SourceFile::new("identity.ash", "1 + 2\n").expect("test source should fit");
    let before = elaborated(&source);

    let after = validate(
        identity_traversal(&before).expect("validated Core should traverse"),
        &[&source],
    )
    .expect("identity output should independently validate");

    let before_root = before.node(before.root()).expect("validated root");
    let after_root = after.node(after.root()).expect("validated root");
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
        let before_child = before.node(before_child).expect("validated child");
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

    let before_evaluation = evaluate(&before).expect("validated input should evaluate");
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
    let source = SourceFile::new(
        "identity-all.ash",
        include_str!("fixtures/first-stratum/valid/v008-mixed.ash"),
    )
    .expect("fixture should fit");
    let before = elaborated(&source);
    let after = validate(
        identity_traversal(&before).expect("validated Core should traverse"),
        &[&source],
    )
    .expect("identity output should validate");
    let remapped = assert_exact_core(&before, &after);

    let before_evaluation = evaluate(&before).expect("validated input should evaluate");
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

    for (name, text) in [
        ("boolean", "true\n"),
        ("unit", "()\n"),
        ("equal", "1 == 1\n"),
    ] {
        let source =
            SourceFile::new(format!("identity-{name}.ash"), text).expect("test source should fit");
        let before = elaborated(&source);
        let after = validate(
            identity_traversal(&before).expect("validated Core should traverse"),
            &[&source],
        )
        .expect("identity output should validate");
        let _ = assert_exact_core(&before, &after);
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
