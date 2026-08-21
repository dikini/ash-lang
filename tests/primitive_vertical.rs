use ash::{
    core::{Primitive, PureComputation, PureExprKind, PureValue, validate},
    elaborate::{ElaborationFailure, Elaborator, TypeContext, TypeError, TypeReason},
    eval::{RuntimeFailure, TraceEvent, Value, evaluate},
    integer::Integer,
    lexer::lex,
    parser::{parse, project},
    resolve::resolve,
    resolved::{ResolvedExpr, ResolvedProgram},
    source::{Origin, SourceFile},
    types::Type,
};

fn resolved(source: &SourceFile) -> ResolvedProgram {
    let lexed = lex(source).expect("test source should lex");
    assert!(lexed.diagnostics.is_empty());
    let tree = parse(lexed);
    assert!(tree.parse_diagnostics().is_empty());
    let surface = project(source, &tree).expect("test source should project");
    resolve(&surface).expect("test source should resolve")
}

fn elaborate_expression(
    text: &str,
) -> (
    SourceFile,
    ResolvedProgram,
    Elaborator,
    ash::elaborate::TypedNode,
) {
    let source = SourceFile::new("primitive.ash", text).expect("test source should fit");
    let program = resolved(&source);
    let mut elaborator = Elaborator::for_program(&program).expect("binder reservation should fit");
    let typed = elaborator
        .synthesize(&program.result, &TypeContext::new())
        .expect("test expression should synthesize");
    (source, program, elaborator, typed)
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
    let source = SourceFile::new("check.ash", "1\n").expect("test source should fit");
    let program = resolved(&source);
    let mut elaborator = Elaborator::for_program(&program).expect("binder reservation should fit");

    let checked = elaborator
        .check(&program.result, &Type::Int, &TypeContext::new())
        .expect("Int should check against Int");
    assert_eq!(checked.ty, Type::Int);

    let error = elaborator
        .check(&program.result, &Type::Bool, &TypeContext::new())
        .expect_err("Int must not check against Bool");
    let TypeError::Mismatch(mismatch) = error else {
        panic!("expected a structural type mismatch");
    };
    assert_eq!(mismatch.expected(), &Type::Bool);
    assert_eq!(mismatch.found(), &Type::Int);
}

#[test]
fn operator_operand_errors_identify_the_incorrect_left_operand() {
    let source = SourceFile::new("left.ash", "true + 1\n").expect("test source should fit");
    let program = resolved(&source);
    let mut elaborator = Elaborator::for_program(&program).expect("binder reservation should fit");

    let error = elaborator
        .synthesize(&program.result, &TypeContext::new())
        .expect_err("Boolean addition must be rejected");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected a source type diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::OperatorOperand);
    assert_eq!(diagnostic.primary.span().range().start(), 0);
    assert_eq!(diagnostic.primary.span().range().end(), 4);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span().range().start(), 5);
    assert_eq!(diagnostic.related[0].span().range().end(), 6);
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
}

#[test]
fn operator_operand_errors_identify_the_incorrect_right_operand() {
    let source = SourceFile::new("right.ash", "1 + true\n").expect("test source should fit");
    let program = resolved(&source);
    let mut elaborator = Elaborator::for_program(&program).expect("binder reservation should fit");

    let error = elaborator
        .synthesize(&program.result, &TypeContext::new())
        .expect_err("Boolean addition must be rejected");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected a source type diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::OperatorOperand);
    assert_eq!(diagnostic.primary.span().range().start(), 4);
    assert_eq!(diagnostic.primary.span().range().end(), 8);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span().range().start(), 2);
    assert_eq!(diagnostic.related[0].span().range().end(), 3);
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
}

#[test]
fn source_type_failure_poisoning_prevents_partial_core_escape() {
    let accepted_source = SourceFile::new("accepted.ash", "1\n").expect("test source should fit");
    let accepted = resolved(&accepted_source);
    let rejected_source =
        SourceFile::new("rejected.ash", "true + 1\n").expect("test source should fit");
    let rejected = resolved(&rejected_source);
    let mut elaborator = Elaborator::new();
    let prior = elaborator
        .synthesize(&accepted.result, &TypeContext::new())
        .expect("the first expression should synthesize");

    let error = elaborator
        .synthesize(&rejected.result, &TypeContext::new())
        .expect_err("the operator failure should be preserved");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected the original source diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::OperatorOperand);

    assert!(matches!(
        elaborator.synthesize(&accepted.result, &TypeContext::new()),
        Err(TypeError::Internal(ElaborationFailure::InvalidState))
    ));
    assert!(matches!(
        elaborator.finish(prior.node),
        Err(ElaborationFailure::InvalidState)
    ));
}

#[test]
fn check_mismatch_poisoning_prevents_partial_core_escape() {
    let source = SourceFile::new("mismatch.ash", "1\n").expect("test source should fit");
    let program = resolved(&source);
    let mut elaborator = Elaborator::for_program(&program).expect("binder reservation should fit");
    let prior = elaborator
        .synthesize(&program.result, &TypeContext::new())
        .expect("the first expression should synthesize");

    let error = elaborator
        .check(&program.result, &Type::Bool, &TypeContext::new())
        .expect_err("the structural mismatch should be preserved");
    let TypeError::Mismatch(mismatch) = error else {
        panic!("expected the original structural mismatch");
    };
    assert_eq!(mismatch.expected(), &Type::Bool);
    assert_eq!(mismatch.found(), &Type::Int);

    assert!(matches!(
        elaborator.check(&program.result, &Type::Int, &TypeContext::new()),
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
    let (source, program, elaborator, typed) = elaborate_expression(text);
    let validated = validate(
        elaborator
            .finish(typed.node)
            .expect("root should belong to builder"),
        &[&source],
    )
    .expect("elaborated Core should validate independently");

    let root = validated.node(validated.root()).expect("validated root");
    assert_eq!(root.ty, Type::Int);
    assert_eq!(root.origin.primary_span(), program.result.span);
    let PureExprKind::Computation(PureComputation::Primitive(operation)) = &root.kind else {
        panic!("expected primitive Core");
    };
    assert_eq!(operation.primitive(), Primitive::Add);
    assert_eq!(
        root.origin.related_spans(),
        &[operation_span(&program.result)]
    );

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
    let source = SourceFile::new("machine.ash", text).expect("test source should fit");
    let program = resolved(&source);
    let mut elaborator = Elaborator::for_program(&program).expect("binder reservation should fit");
    let typed = elaborator
        .synthesize(&program.result, &TypeContext::new())
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

    assert_eq!(
        evaluation.value,
        Value::Integer(Integer::parse_decimal("7").expect("valid test integer"))
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
    assert_eq!(unit.value, Value::Unit);

    let equality =
        evaluate(&validated_expression("(20 + 1) == 21\n")).expect("equality should evaluate");
    assert_eq!(equality.value, Value::Boolean(true));
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
fn machine_returns_a_typed_failure_for_a_pending_validated_core_form() {
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

    let error = evaluate(&validated).expect_err("functions arrive in the next machine increment");
    assert_eq!(error, RuntimeFailure::UnsupportedForm);
}
