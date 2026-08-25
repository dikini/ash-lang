use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{Primitive, PureComputation, PureExprKind, PureValue, validate},
    elaborate::{ElaborationFailure, Elaborator, TypeContext, TypeError, TypeReason},
    eval::{TraceEvent, Value, evaluate},
    integer::Integer,
    module::{ModuleRoots, load_module_graph},
    resolve::resolve_module,
    resolved::{ResolvedDefinitionKind, ResolvedExpr},
    source::{Origin, SourceFile},
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempModule(PathBuf);

impl TempModule {
    fn write(source: &str) -> Self {
        let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "ash-primitive-vertical-{}-{id}.ash",
            std::process::id()
        ));
        fs::write(&path, source).expect("module fixture should be writable");
        Self(path)
    }
}

impl Drop for TempModule {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn resolved(text: &str) -> (SourceFile, ResolvedExpr) {
    let module = TempModule::write(&format!("main : Unit -> Unit\nmain () = {text}"));
    let graph =
        load_module_graph(&module.0, &ModuleRoots::empty()).expect("module fixture should load");
    let loaded = graph
        .module(graph.entry())
        .expect("entry module should be retained");
    let source = loaded.source().clone();
    let resolved = resolve_module(loaded, &[]).expect("module fixture should resolve");
    let definition = resolved
        .definitions()
        .iter()
        .find(|definition| {
            matches!(
                &definition.kind,
                ResolvedDefinitionKind::Equational(global)
                    if global.interface.name.spelling == "main"
            )
        })
        .expect("module fixture should retain main");
    let ResolvedDefinitionKind::Equational(main) = &definition.kind else {
        unreachable!("the selected definition is equational")
    };
    let expression = main
        .equations
        .first()
        .expect("main should have one equation")
        .body
        .clone();
    (source, expression)
}

fn elaborate_expression(
    text: &str,
) -> (
    SourceFile,
    ResolvedExpr,
    Elaborator,
    ash::elaborate::TypedNode,
) {
    let (source, expression) = resolved(text);
    let mut elaborator = Elaborator::new();
    let typed = elaborator
        .synthesize(&expression, &TypeContext::new())
        .expect("test expression should synthesize");
    (source, expression, elaborator, typed)
}

#[test]
fn literal_rules_synthesize_the_closed_primitive_types() {
    for (text, expected) in [
        ("1\n", Type::Int),
        ("true\n", Type::Bool),
        ("()\n", Type::Unit),
    ] {
        let (_, _, _, typed) = elaborate_expression(text);
        assert_eq!(typed.ty, expected);
    }
}

#[test]
fn primitive_rules_synthesize_their_structural_result_types() {
    for (text, expected) in [
        ("1 + 2\n", Type::Int),
        ("2 * 3\n", Type::Int),
        ("4 == 4\n", Type::Bool),
    ] {
        let (_, _, _, typed) = elaborate_expression(text);
        assert_eq!(typed.ty, expected);
    }
}

#[test]
fn check_uses_the_named_structural_equality_rule() {
    let (_, expression) = resolved("1\n");
    let mut elaborator = Elaborator::new();

    let checked = elaborator
        .check(&expression, &Type::Int, &TypeContext::new())
        .expect("Int should check against Int");
    assert_eq!(checked.ty, Type::Int);

    let error = elaborator
        .check(&expression, &Type::Bool, &TypeContext::new())
        .expect_err("Int must not check against Bool");
    let TypeError::Mismatch(mismatch) = error else {
        panic!("expected a structural type mismatch");
    };
    assert_eq!(mismatch.expected(), &Type::Bool);
    assert_eq!(mismatch.found(), &Type::Int);
}

#[test]
fn operator_operand_errors_identify_the_incorrect_left_operand() {
    let (_, expression) = resolved("true + 1\n");
    let mut elaborator = Elaborator::new();

    let error = elaborator
        .synthesize(&expression, &TypeContext::new())
        .expect_err("Boolean addition must be rejected");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected a source type diagnostic");
    };
    let ash::resolved::ResolvedExprKind::Add(operation) = &expression.kind else {
        panic!("expected resolved addition")
    };

    assert_eq!(diagnostic.reason, TypeReason::OperatorOperand);
    assert_eq!(diagnostic.primary.span(), operation.left.span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), operation.operator_span);
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
}

#[test]
fn operator_operand_errors_identify_the_incorrect_right_operand() {
    let (_, expression) = resolved("1 + true\n");
    let mut elaborator = Elaborator::new();

    let error = elaborator
        .synthesize(&expression, &TypeContext::new())
        .expect_err("Boolean addition must be rejected");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected a source type diagnostic");
    };
    let ash::resolved::ResolvedExprKind::Add(operation) = &expression.kind else {
        panic!("expected resolved addition")
    };

    assert_eq!(diagnostic.reason, TypeReason::OperatorOperand);
    assert_eq!(diagnostic.primary.span(), operation.right.span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), operation.operator_span);
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
}

#[test]
fn source_type_failure_poisoning_prevents_partial_core_escape() {
    let (_, accepted) = resolved("1\n");
    let (_, rejected) = resolved("true + 1\n");
    let mut elaborator = Elaborator::new();
    let prior = elaborator
        .synthesize(&accepted, &TypeContext::new())
        .expect("the first expression should synthesize");

    let error = elaborator
        .synthesize(&rejected, &TypeContext::new())
        .expect_err("the operator failure should be preserved");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected the original source diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::OperatorOperand);

    assert!(matches!(
        elaborator.synthesize(&accepted, &TypeContext::new()),
        Err(TypeError::Internal(ElaborationFailure::InvalidState))
    ));
    assert!(matches!(
        elaborator.finish(prior.node),
        Err(ElaborationFailure::InvalidState)
    ));
}

#[test]
fn check_mismatch_poisoning_prevents_partial_core_escape() {
    let (_, expression) = resolved("1\n");
    let mut elaborator = Elaborator::new();
    let prior = elaborator
        .synthesize(&expression, &TypeContext::new())
        .expect("the first expression should synthesize");

    let error = elaborator
        .check(&expression, &Type::Bool, &TypeContext::new())
        .expect_err("the structural mismatch should be preserved");
    let TypeError::Mismatch(mismatch) = error else {
        panic!("expected the original structural mismatch");
    };
    assert_eq!(mismatch.expected(), &Type::Bool);
    assert_eq!(mismatch.found(), &Type::Int);

    assert!(matches!(
        elaborator.check(&expression, &Type::Int, &TypeContext::new()),
        Err(TypeError::Internal(ElaborationFailure::InvalidState))
    ));
    assert!(matches!(
        elaborator.finish(prior.node),
        Err(ElaborationFailure::InvalidState)
    ));
}

#[test]
fn elaboration_preserves_arbitrary_precision_and_causal_origins() {
    let text = "340282366920938463463374607431768211456 + 1\n";
    let (source, expression, elaborator, typed) = elaborate_expression(text);
    let validated = validate(
        elaborator
            .finish(typed.node)
            .expect("root should belong to builder"),
        &[&source],
    )
    .expect("elaborated Core should validate independently");

    let root = validated.node(validated.root()).expect("validated root");
    assert_eq!(root.ty, Type::Int);
    assert_eq!(root.origin.primary_span(), expression.span);
    let PureExprKind::Computation(PureComputation::Primitive(operation)) = &root.kind else {
        panic!("expected primitive Core");
    };
    assert_eq!(operation.primitive(), Primitive::Add);
    assert_eq!(root.origin.related_spans(), &[operation_span(&expression)]);

    let left = validated
        .node(operation.left())
        .expect("validated left operand");
    assert_eq!(left.origin, Origin::Source(left.origin.primary_span()));
    let PureExprKind::Value(PureValue::Integer(integer)) = &left.kind else {
        panic!("expected integer Core");
    };
    assert_eq!(
        integer.value().to_string(),
        "340282366920938463463374607431768211456"
    );
}

fn operation_span(expression: &ResolvedExpr) -> ash::source::Span {
    match &expression.kind {
        ash::resolved::ResolvedExprKind::Add(binary)
        | ash::resolved::ResolvedExprKind::Multiply(binary)
        | ash::resolved::ResolvedExprKind::Equal(binary) => binary.operator_span,
        _ => panic!("expected primitive expression"),
    }
}

fn validated_expression(text: &str) -> ash::core::ValidatedProgram {
    let (source, expression) = resolved(text);
    let mut elaborator = Elaborator::new();
    let typed = elaborator
        .synthesize(&expression, &TypeContext::new())
        .expect("test expression should synthesize");
    validate(
        elaborator.finish(typed.node).expect("root should finish"),
        &[&source],
    )
    .expect("elaborated Core should validate")
}

#[test]
fn machine_evaluates_v001_with_left_to_right_entry_events() {
    let program = validated_expression("1 + 2 * 3\n");
    let evaluation = evaluate(&program).expect("validated primitive Core should evaluate");

    let Value::Integer(value) = evaluation.value else {
        panic!("expected an integer value");
    };
    assert_eq!(
        value,
        Integer::parse_decimal("7").expect("valid test integer")
    );
    let entered = evaluation
        .trace
        .iter()
        .map(|event| match event {
            TraceEvent::Enter(node) => node.value(),
        })
        .collect::<Vec<_>>();
    assert_eq!(entered, vec![4, 0, 3, 1, 2]);
}

#[test]
fn machine_evaluates_unit_and_integer_equality_values() {
    let unit = evaluate(&validated_expression("()\n")).expect("unit should evaluate");
    assert!(matches!(unit.value, Value::Unit));

    let equality =
        evaluate(&validated_expression("(20 + 1) == 21\n")).expect("equality should evaluate");
    assert!(matches!(equality.value, Value::Boolean(true)));
}

#[test]
fn machine_arithmetic_does_not_overflow_host_integers() {
    let evaluation = evaluate(&validated_expression(
        "340282366920938463463374607431768211456 * 340282366920938463463374607431768211456\n",
    ))
    .expect("mathematical multiplication should evaluate");

    assert_eq!(
        evaluation.value.to_string(),
        "115792089237316195423570985008687907853269984665640564039457584007913129639936"
    );
}

#[test]
fn machine_returns_an_inspectable_closure_for_validated_function_core() {
    let source =
        SourceFile::new("function.ash", "fn(value) { value }\n").expect("test source should fit");
    let origin = Origin::Source(
        source
            .span(ash::source::ByteRange::new(0, 18).expect("ordered range"))
            .expect("range should fit"),
    );
    let mut builder = ash::core::CoreBuilder::new();
    let parameter = builder
        .binder(Type::Int, origin.clone())
        .expect("test binder should fit");
    let body = builder
        .variable(parameter.id(), Type::Int, origin.clone())
        .expect("test body should fit");
    let function = builder
        .function(
            parameter,
            body,
            Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
            origin,
        )
        .expect("test function should fit");
    let validated = validate(
        builder.finish(function).expect("test root should fit"),
        &[&source],
    )
    .expect("function Core should validate");

    let evaluation = evaluate(&validated).expect("validated functions should evaluate");
    let Value::Function(closure) = evaluation.value else {
        panic!("expected a function value");
    };
    assert_eq!(closure.parameter.local(), 0);
    assert_eq!(closure.body.value(), 0);
    assert!(closure.environment.is_empty());
    assert_eq!(evaluation.trace, vec![TraceEvent::Enter(validated.root())]);
}
