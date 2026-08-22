use std::{
    fs,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{PureComputation, PureExprKind, PureValue, validate},
    driver::{PipelineFailure, run_source},
    elaborate::{ElaborationFailure, Elaborator, TypeContext, TypeError, TypeReason},
    eval::{TraceEvent, Value, evaluate},
    lexer::lex,
    parser::{parse, project},
    resolve::resolve,
    resolved::{ResolvedDefinitionKind, ResolvedExprKind, ResolvedProgram},
    source::{GeneratedReason, SourceFile},
    types::Type,
};

const V002_EQUATIONAL: &str = include_str!("fixtures/first-stratum/valid/v002-equational.ash");
const V002_OPERATIONAL: &str = include_str!("fixtures/first-stratum/valid/v002-operational.ash");
const V004: &str = include_str!("fixtures/first-stratum/valid/v004-capture.ash");
const V005: &str = include_str!("fixtures/first-stratum/valid/v005-higher-order.ash");
const V008: &str = include_str!("fixtures/first-stratum/valid/v008-mixed.ash");

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempFile(PathBuf);

impl TempFile {
    fn write(text: &str) -> Self {
        let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ash-functions-{}-{id}.ash", std::process::id()));
        fs::write(&path, text).expect("test input should be writable");
        Self(path)
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn resolved(source: &SourceFile) -> ResolvedProgram {
    let lexed = lex(source).expect("test source should lex");
    assert!(lexed.diagnostics.is_empty());
    let tree = parse(lexed);
    assert!(tree.parse_diagnostics().is_empty());
    let surface = project(source, &tree).expect("test source should project");
    resolve(&surface).expect("test source should resolve")
}

fn validated_program(
    source: &SourceFile,
    program: &ResolvedProgram,
) -> (ash::core::ValidatedProgram, Type) {
    let mut elaborator = Elaborator::for_program(program).expect("binder reservation should fit");
    let typed = elaborator
        .synthesize_program(program)
        .expect("program should elaborate");
    let ty = typed.ty;
    let unchecked = elaborator.finish(typed.node).expect("root should finish");
    let validated = validate(unchecked, &[source]).expect("function Core should validate");
    (validated, ty)
}

#[test]
fn anonymous_function_checks_only_with_a_structural_function_context() {
    let source = SourceFile::new("anonymous.ash", "fn(value) {\n    value\n}\n")
        .expect("test source should fit");
    let program = resolved(&source);
    let expected = Type::Function(Box::new(Type::Int), Box::new(Type::Int));
    let mut elaborator = Elaborator::for_program(&program).expect("binder reservation should fit");

    let typed = elaborator
        .check(&program.result, &expected, &TypeContext::new())
        .expect("the expected arrow should check the anonymous function");
    assert_eq!(typed.ty, expected);
    let validated = validate(
        elaborator.finish(typed.node).expect("root should finish"),
        &[&source],
    )
    .expect("checked function Core should validate independently");
    let root = validated.node(validated.root()).expect("function root");
    let PureExprKind::Value(PureValue::Function(function)) = &root.kind else {
        panic!("expected shared function Core");
    };
    let ResolvedExprKind::Function(surface_function) = &program.result.kind else {
        panic!("expected resolved anonymous function");
    };
    assert_eq!(function.parameter().id(), surface_function.parameter.id);
    assert_eq!(function.parameter().ty(), &Type::Int);
    assert_eq!(
        root.origin.generated_reason(),
        Some(GeneratedReason::FunctionLowering)
    );
}

#[test]
fn anonymous_function_synthesis_has_the_specific_missing_context_reason_and_span() {
    let source = SourceFile::new("missing-context.ash", "fn(value) {\n    value\n}\n")
        .expect("test source should fit");
    let program = resolved(&source);
    let mut elaborator = Elaborator::for_program(&program).expect("binder reservation should fit");

    let error = elaborator
        .synthesize(&program.result, &TypeContext::new())
        .expect_err("anonymous functions do not synthesize");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected a source type diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), program.result.span);
    assert!(diagnostic.related.is_empty());
}

#[test]
fn anonymous_function_with_a_non_function_expectation_uses_the_current_context_category() {
    let source = SourceFile::new("non-function-context.ash", "fn(value) {\n    value\n}\n")
        .expect("test source should fit");
    let program = resolved(&source);
    let mut elaborator = Elaborator::for_program(&program).expect("binder reservation should fit");

    let error = elaborator
        .check(&program.result, &Type::Int, &TypeContext::new())
        .expect_err("an Int expectation is not a function context");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected the current source diagnostic category");
    };
    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), program.result.span);
}

#[test]
fn application_rejects_a_non_function_at_the_function_position() {
    let text = "1 2\n";
    let source = SourceFile::new("not-applicable.ash", text).expect("test source should fit");
    let program = resolved(&source);
    let ResolvedExprKind::Apply(application) = &program.result.kind else {
        panic!("expected an application");
    };

    let error = run_source(source).expect_err("an integer is not applicable");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected a source type diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::NotApplicable);
    assert_eq!(diagnostic.primary.span(), application.function.span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), program.result.span);
    assert_eq!(diagnostic.expected.as_deref(), Some("function"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
}

#[test]
fn application_argument_mismatch_relates_the_argument_to_the_global_domain_annotation() {
    let text = "increment : Int -> Int\nincrement value = value + 1\n\nincrement true\n";
    let source = SourceFile::new("argument.ash", text).expect("test source should fit");
    let program = resolved(&source);
    let ResolvedDefinitionKind::Equational(definition) = &program.definitions[0].kind else {
        panic!("expected an equational definition");
    };
    let ResolvedExprKind::Apply(application) = &program.result.kind else {
        panic!("expected an application");
    };

    let error = run_source(source).expect_err("Bool does not check against the Int domain");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected a source type diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::Argument);
    assert_eq!(diagnostic.primary.span(), application.argument.span);
    assert!(diagnostic.related.iter().any(|label| {
        definition
            .interface
            .annotation
            .provenance
            .function_parts()
            .is_some_and(|(domain, _)| domain.span() == Some(label.span()))
    }));
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
}

#[test]
fn equational_returned_function_argument_uses_the_inner_domain_provenance() {
    let text =
        "make : Unit -> Int -> Int\nmake ignored = fn(value) {\n    value\n}\n\nmake () true\n";
    let source =
        SourceFile::new("equational-returned-function.ash", text).expect("source should fit");
    let program = resolved(&source);
    let ResolvedDefinitionKind::Equational(definition) = &program.definitions[0].kind else {
        panic!("expected an equational definition");
    };
    let (outer_domain, returned) = definition
        .interface
        .annotation
        .provenance
        .function_parts()
        .expect("expected an outer function type");
    let (returned_domain, _) = returned
        .function_parts()
        .expect("expected a returned function type");

    let error = run_source(source).expect_err("Bool does not match the returned Int domain");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected an application argument diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::Argument);
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
    assert!(
        diagnostic
            .related
            .iter()
            .any(|label| Some(label.span()) == returned_domain.span())
    );
    assert!(
        !diagnostic
            .related
            .iter()
            .any(|label| Some(label.span()) == outer_domain.span())
    );
}

#[test]
fn operational_returned_function_argument_uses_the_inner_domain_provenance() {
    let text = "fn make(ignored : Unit) -> Int -> Int {\n    fn(value) {\n        value\n    }\n}\n\nmake () true\n";
    let source =
        SourceFile::new("operational-returned-function.ash", text).expect("source should fit");
    let program = resolved(&source);
    let ResolvedDefinitionKind::InlineOperational(definition) = &program.definitions[0].kind else {
        panic!("expected an operational definition");
    };
    let (returned_domain, _) = definition
        .header
        .result_type
        .provenance
        .function_parts()
        .expect("expected a returned function type");

    let error = run_source(source).expect_err("Bool does not match the returned Int domain");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected an application argument diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::Argument);
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
    assert!(
        diagnostic
            .related
            .iter()
            .any(|label| Some(label.span()) == returned_domain.span())
    );
    assert!(
        !diagnostic
            .related
            .iter()
            .any(|label| { label.span() == definition.header.parameter.annotation.span })
    );
}

#[test]
fn both_v002_presentations_converge_to_function_and_recursive_core_with_distinct_origins() {
    let equational_source =
        SourceFile::new("v002-equational.ash", V002_EQUATIONAL).expect("fixture should fit");
    let operational_source =
        SourceFile::new("v002-operational.ash", V002_OPERATIONAL).expect("fixture should fit");
    let equational = resolved(&equational_source);
    let operational = resolved(&operational_source);
    let (equational_core, equational_type) = validated_program(&equational_source, &equational);
    let (operational_core, operational_type) = validated_program(&operational_source, &operational);

    assert_eq!(equational_type, Type::Int);
    assert_eq!(operational_type, Type::Int);
    let equational_root = equational_core.node(equational_core.root()).expect("root");
    let operational_root = operational_core
        .node(operational_core.root())
        .expect("root");
    let PureExprKind::Computation(PureComputation::RecursiveBind(equational_group)) =
        &equational_root.kind
    else {
        panic!("expected an outer recursive group");
    };
    let PureExprKind::Computation(PureComputation::RecursiveBind(operational_group)) =
        &operational_root.kind
    else {
        panic!("expected an outer recursive group");
    };
    let equational_function = equational_core
        .node(equational_group.members()[0].initializer())
        .expect("equational function");
    let operational_function = operational_core
        .node(operational_group.members()[0].initializer())
        .expect("operational function");
    assert!(matches!(
        equational_function.kind,
        PureExprKind::Value(PureValue::Function(_))
    ));
    assert!(matches!(
        operational_function.kind,
        PureExprKind::Value(PureValue::Function(_))
    ));
    assert_eq!(equational_function.ty, operational_function.ty);
    assert_eq!(
        equational_function.origin.generated_reason(),
        Some(GeneratedReason::FunctionLowering)
    );
    assert_eq!(
        operational_function.origin.generated_reason(),
        Some(GeneratedReason::FunctionLowering)
    );
    assert_ne!(
        equational_function.origin.primary_span().range(),
        operational_function.origin.primary_span().range()
    );
}

#[test]
fn a_mid_program_type_failure_poisons_completion_and_cannot_expose_partial_core() {
    let text = "first : Int -> Int\nfirst value = value\n\nsecond : Int -> Bool\nsecond value = value\n\n1\n";
    let source = SourceFile::new("poisoned-program.ash", text).expect("test source should fit");
    let program = resolved(&source);
    let mut elaborator = Elaborator::for_program(&program).expect("binder reservation should fit");

    let error = elaborator
        .synthesize_program(&program)
        .expect_err("the second definition result should be rejected");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected the definition-result diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::DefinitionResult);
    assert!(matches!(
        elaborator.synthesize(&program.result, &TypeContext::new()),
        Err(TypeError::Internal(ElaborationFailure::InvalidState))
    ));
}

#[test]
fn a_later_global_types_and_runs_with_an_earlier_global_in_lexical_scope() {
    let text = "first : Int -> Int\nfirst value = value + 1\n\nsecond : Int -> Int\nsecond value = first value\n\nsecond 41\n";
    let source = SourceFile::new("sequential-global-scope.ash", text).expect("source should fit");

    let observation = run_source(source).expect("the completed first global should be in scope");

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn definition_result_mismatch_relates_the_body_to_the_declared_codomain() {
    let text = "wrong : Int -> Bool\nwrong value = value\n\n1\n";
    let source = SourceFile::new("definition-result.ash", text).expect("source should fit");
    let program = resolved(&source);
    let ResolvedDefinitionKind::Equational(definition) = &program.definitions[0].kind else {
        panic!("expected an equational definition");
    };
    let (_, codomain) = definition
        .interface
        .annotation
        .provenance
        .function_parts()
        .expect("expected a function interface");

    let error = run_source(source).expect_err("the declared Bool result should reject Int");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected a source type diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::DefinitionResult);
    assert_eq!(diagnostic.primary.span(), definition.equation.body.span);
    assert!(
        diagnostic
            .related
            .iter()
            .any(|label| Some(label.span()) == codomain.span())
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("Bool"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
}

#[test]
fn equational_interface_must_expose_one_function_domain() {
    let text = "answer : Int\nanswer value = value\n\n1\n";
    let source = SourceFile::new("interface-shape.ash", text).expect("source should fit");
    let program = resolved(&source);
    let ResolvedDefinitionKind::Equational(definition) = &program.definitions[0].kind else {
        panic!("expected an equational definition");
    };

    let error = run_source(source).expect_err("a non-function interface has no equation rule");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected a source type diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::EquationInterfaceNotFunction);
    assert_eq!(
        diagnostic.primary.span(),
        definition.interface.annotation.span
    );
    assert!(
        diagnostic
            .related
            .iter()
            .any(|label| { label.span() == definition.equation.name.origin.primary_span() })
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("function"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
}

#[test]
fn every_task9_corpus_program_evaluates_to_42_as_an_int() {
    for (name, text) in [
        ("v002-equational.ash", V002_EQUATIONAL),
        ("v002-operational.ash", V002_OPERATIONAL),
        ("v004-capture.ash", V004),
        ("v005-higher-order.ash", V005),
        ("v008-mixed.ash", V008),
    ] {
        let source = SourceFile::new(name, text).expect("fixture should fit");
        let observation = run_source(source).expect("valid function program should run");
        assert_eq!(observation.value.to_string(), "42", "{name}");
        assert_eq!(observation.ty, Type::Int, "{name}");
    }
}

#[test]
fn a_returned_function_exposes_its_code_origin_and_captured_environment() {
    let text = "{\n    let offset = 40\n    let add_offset : Int -> Int = fn(value) {\n        value + offset\n    }\n    add_offset\n}\n";
    let source = SourceFile::new("returned-function.ash", text).expect("source should fit");
    let observation = run_source(source).expect("function value should evaluate");
    let Value::Function(closure) = observation.value else {
        panic!("expected an inspectable function value");
    };

    assert_eq!(closure.environment.len(), 1);
    assert!(closure.program.node(closure.body).is_some());
    assert_eq!(
        closure.origin.generated_reason(),
        Some(GeneratedReason::FunctionLowering)
    );
    assert_eq!(observation.ty.to_string(), "Int -> Int");
    let debug = format!("{closure:?}");
    assert!(debug.contains("Closure"));
    assert!(!debug.contains("nodes:"));
}

#[test]
fn an_escaped_function_uses_its_captured_environment_not_the_caller_environment() {
    let text = "{\n    let escaped : Unit -> Int = {\n        let captured = 42\n        fn(ignored) {\n            captured\n        }\n    }\n    escaped ()\n}\n";
    let source = SourceFile::new("escaped-capture.ash", text).expect("source should fit");
    let observation = run_source(source).expect("the escaped closure should retain captured");

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn application_trace_enters_function_before_argument_then_runs_the_closure_body() {
    let source =
        SourceFile::new("v002-equational.ash", V002_EQUATIONAL).expect("fixture should fit");
    let program = resolved(&source);
    let (validated, _) = validated_program(&source, &program);
    let root = validated.node(validated.root()).expect("global binding");
    let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &root.kind else {
        panic!("expected global recursive group");
    };
    let application = validated.node(group.body()).expect("application");
    let PureExprKind::Computation(PureComputation::Apply(application)) = &application.kind else {
        panic!("expected application Core");
    };
    let function = validated
        .node(group.members()[0].initializer())
        .expect("function initializer");
    let PureExprKind::Value(PureValue::Function(function)) = &function.kind else {
        panic!("expected function Core");
    };
    let function_body = validated.node(function.body()).expect("function body");
    let PureExprKind::Computation(PureComputation::Primitive(function_body)) = &function_body.kind
    else {
        panic!("expected primitive function body");
    };

    let evaluation = evaluate(&validated).expect("function Core should evaluate");
    assert_eq!(evaluation.value.to_string(), "42");
    let entered = evaluation
        .trace
        .iter()
        .map(|event| match event {
            TraceEvent::Enter(node) => *node,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        entered,
        vec![
            validated.root(),
            group.body(),
            application.function(),
            application.argument(),
            function.body(),
            function_body.left(),
            function_body.right(),
        ]
    );
}

#[test]
fn cli_observes_a_global_function_opaquely_with_an_unambiguous_arrow_type() {
    let source = TempFile::write("identity : Int -> Int\nidentity value = value\n\nidentity\n");
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(&source.0)
        .output()
        .expect("the Ash executable should start");

    assert!(output.status.success());
    assert_eq!(output.stdout, b"<function> : Int -> Int\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn each_task9_fixture_has_the_exact_cli_observation() {
    for path in [
        "tests/fixtures/first-stratum/valid/v002-equational.ash",
        "tests/fixtures/first-stratum/valid/v002-operational.ash",
        "tests/fixtures/first-stratum/valid/v004-capture.ash",
        "tests/fixtures/first-stratum/valid/v005-higher-order.ash",
        "tests/fixtures/first-stratum/valid/v008-mixed.ash",
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_ash"))
            .arg(path)
            .output()
            .expect("the Ash executable should start");
        assert!(output.status.success(), "{path}");
        assert_eq!(output.stdout, b"42 : Int\n", "{path}");
        assert!(output.stderr.is_empty(), "{path}");
    }
}

#[test]
fn structural_arrow_rendering_parenthesizes_only_a_function_domain() {
    let higher_order = Type::Function(
        Box::new(Type::Function(Box::new(Type::Int), Box::new(Type::Int))),
        Box::new(Type::Function(Box::new(Type::Bool), Box::new(Type::Unit))),
    );

    assert_eq!(higher_order.to_string(), "(Int -> Int) -> Bool -> Unit");
}
