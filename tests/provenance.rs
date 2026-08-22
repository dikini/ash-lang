use ash::{
    core::{PureComputation, PureExprKind, PureValue, validate},
    driver::{PipelineFailure, run_source},
    elaborate::{Elaborator, TypeError, TypeReason},
    lexer::lex,
    parser::{parse, project},
    resolve::resolve,
    resolved::{
        ResolvedDefinitionKind, ResolvedExprKind, ResolvedLocalDeclaration, ResolvedProgram,
    },
    source::{GeneratedReason, Origin, SourceFile, Span},
};

fn resolved(source: &SourceFile) -> ResolvedProgram {
    let lexed = lex(source).expect("test source should lex");
    assert!(lexed.diagnostics.is_empty());
    let tree = parse(lexed);
    assert!(tree.parse_diagnostics().is_empty());
    let surface = project(source, &tree).expect("test source should project");
    resolve(&surface).expect("test source should resolve")
}

fn validated(source: &SourceFile, program: &ResolvedProgram) -> ash::core::ValidatedProgram {
    let mut elaborator = Elaborator::for_program(program).expect("binder namespace should fit");
    let typed = elaborator
        .synthesize_program(program)
        .expect("test program should elaborate");
    validate(
        elaborator.finish(typed.node).expect("root should finish"),
        &[source],
    )
    .expect("elaborated Core should validate")
}

fn assert_check_origin(origin: &Origin, expression: Span, expected: Span) {
    let Origin::Generated { cause, reason } = origin else {
        panic!("successful checking should retain a generated origin")
    };
    assert_eq!(reason, &GeneratedReason::TypeChecking);
    assert_eq!(cause.primary_span(), expression);
    assert!(cause.related_spans().contains(&expected));
}

#[test]
fn recursive_group_retains_group_member_function_and_occurrence_causes() {
    let source = SourceFile::new(
        "recursive-origins.ash",
        "{\nlet rec repeat : Unit -> Int = fn(ignored) {\nrepeat ()\n}\nrepeat ()\n}\n",
    )
    .expect("test source should fit");
    let program = resolved(&source);
    let ResolvedExprKind::Block(block) = &program.result.kind else {
        panic!("expected block")
    };
    let ResolvedLocalDeclaration::Recursive(source_group) = &block.declarations[0] else {
        panic!("expected recursive group")
    };
    let source_member = &source_group.members[0];
    let ResolvedExprKind::Function(source_function) = &source_member.initializer.kind else {
        panic!("expected recursive function")
    };
    let ResolvedExprKind::Apply(source_call) = &source_function.body.result.kind else {
        panic!("expected recursive call")
    };

    let core = validated(&source, &program);
    let root = core.node(core.root()).expect("recursive root");
    let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &root.kind else {
        panic!("expected recursive Core group")
    };
    assert_eq!(
        root.origin.generated_reason(),
        Some(GeneratedReason::RecursiveBindingLowering)
    );
    assert_eq!(root.origin.primary_span(), source_group.span);
    for expected in [
        source_member.span,
        source_member.annotation.span,
        source_member.initializer.span,
    ] {
        assert!(root.origin.related_spans().contains(&expected));
    }
    assert_eq!(
        group.members()[0].binder().origin().primary_span(),
        source_member.binder.origin.primary_span()
    );

    let function = core
        .node(group.members()[0].initializer())
        .expect("function initializer");
    assert_eq!(
        function.origin.primary_span(),
        source_member.initializer.span
    );
    let PureExprKind::Value(PureValue::Function(function_node)) = &function.kind else {
        panic!("expected function Core")
    };
    assert_eq!(
        function_node.parameter().origin().primary_span(),
        source_function.parameter.origin.primary_span()
    );
    let body = core.node(function_node.body()).expect("recursive body");
    assert_eq!(body.origin.primary_span(), source_function.body.result.span);
    let PureExprKind::Computation(PureComputation::Apply(call)) = &body.kind else {
        panic!("expected recursive application Core")
    };
    let occurrence = core.node(call.function()).expect("recursive occurrence");
    assert_eq!(occurrence.origin.primary_span(), source_call.function.span);
}

#[test]
fn successful_definition_checks_retain_the_body_and_declared_result_origins() {
    for (path, text) in [
        (
            "equational.ash",
            "increment : Int -> Int\nincrement value = value + 1\n\nincrement 41\n",
        ),
        (
            "operational.ash",
            "fn increment(value : Int) -> Int {\n    value + 1\n}\n\nincrement 41\n",
        ),
    ] {
        let source = SourceFile::new(path, text).expect("test source should fit");
        let program = resolved(&source);
        let core = validated(&source, &program);
        let root = core.node(core.root()).expect("global binding");
        let PureExprKind::Computation(PureComputation::RecursiveBind(global)) = &root.kind else {
            panic!("expected global recursive group")
        };
        let function = core
            .node(global.members()[0].initializer())
            .expect("function initializer");
        let PureExprKind::Value(PureValue::Function(function_node)) = &function.kind else {
            panic!("expected function value")
        };
        let body = core.node(function_node.body()).expect("function body");

        match &program.definitions[0].kind {
            ResolvedDefinitionKind::Equational(definition) => assert_check_origin(
                &body.origin,
                definition.equation.body.span,
                definition
                    .interface
                    .annotation
                    .provenance
                    .function_parts()
                    .expect("expected function annotation")
                    .1
                    .span()
                    .expect("expected codomain provenance"),
            ),
            ResolvedDefinitionKind::InlineOperational(definition) => assert_check_origin(
                &body.origin,
                definition.body.result.span,
                definition.header.result_type.span,
            ),
        }
    }
}

#[test]
fn both_global_presentations_retain_exact_binding_function_parameter_and_application_causes() {
    for (path, text) in [
        (
            "equational-causes.ash",
            "increment : Int -> Int\nincrement value = value + 1\n\nincrement 41\n",
        ),
        (
            "operational-causes.ash",
            "fn increment(value : Int) -> Int {\n    value + 1\n}\n\nincrement 41\n",
        ),
    ] {
        let source = SourceFile::new(path, text).expect("test source should fit");
        let program = resolved(&source);
        let core = validated(&source, &program);
        let definition = &program.definitions[0];
        let root = core.node(core.root()).expect("global binding");
        let PureExprKind::Computation(PureComputation::RecursiveBind(global)) = &root.kind else {
            panic!("expected global recursive group")
        };
        assert_eq!(
            root.origin.generated_reason(),
            Some(GeneratedReason::RecursiveBindingLowering)
        );
        assert_eq!(root.origin.primary_span(), program.span);

        let function = core
            .node(global.members()[0].initializer())
            .expect("function initializer");
        let PureExprKind::Value(PureValue::Function(function_node)) = &function.kind else {
            panic!("expected function value")
        };
        assert_eq!(
            function.origin.generated_reason(),
            Some(GeneratedReason::FunctionLowering)
        );
        assert_eq!(
            function_node.parameter().origin().generated_reason(),
            Some(GeneratedReason::FunctionLowering)
        );

        match &definition.kind {
            ResolvedDefinitionKind::Equational(equational) => {
                assert_eq!(
                    global.members()[0].binder().id(),
                    equational.interface.name.id
                );
                assert_eq!(
                    global.members()[0].binder().origin().primary_span(),
                    equational.interface.name.origin.primary_span()
                );
                assert_eq!(function.origin.primary_span(), equational.equation.span);
                for expected in [
                    definition.span,
                    equational.interface.span,
                    equational.interface.annotation.span,
                    equational.equation.body.span,
                ] {
                    assert!(function.origin.related_spans().contains(&expected));
                }
                assert_eq!(
                    function_node.parameter().origin().primary_span(),
                    equational.equation.binder.origin.primary_span()
                );
            }
            ResolvedDefinitionKind::InlineOperational(operational) => {
                assert_eq!(
                    global.members()[0].binder().id(),
                    operational.header.name.id
                );
                assert_eq!(
                    global.members()[0].binder().origin().primary_span(),
                    operational.header.name.origin.primary_span()
                );
                assert_eq!(function.origin.primary_span(), definition.span);
                for expected in [
                    operational.header.span,
                    operational.header.parameter.annotation.span,
                    operational.header.result_type.span,
                    operational.body.span,
                ] {
                    assert!(function.origin.related_spans().contains(&expected));
                }
                assert_eq!(
                    function_node.parameter().origin().primary_span(),
                    operational.header.parameter.binder.origin.primary_span()
                );
            }
        }

        let application = core
            .node(global.body())
            .expect("program result application");
        let PureExprKind::Computation(PureComputation::Apply(application_node)) = &application.kind
        else {
            panic!("expected application")
        };
        let ash::resolved::ResolvedExprKind::Apply(resolved_application) = &program.result.kind
        else {
            panic!("expected resolved application")
        };
        assert_eq!(application.origin.primary_span(), program.result.span);
        assert_eq!(
            application.origin.related_spans(),
            &[
                resolved_application.function.span,
                resolved_application.argument.span,
            ]
        );
        assert!(core.node(application_node.function()).is_some());
        assert!(core.node(application_node.argument()).is_some());
    }
}

#[test]
fn t001_and_t004_diagnostics_keep_their_source_cause_spans() {
    let t001_source = SourceFile::new(
        "t001.ash",
        "wrong : Int -> Bool\nwrong value = value\n\ntrue\n",
    )
    .expect("test source should fit");
    let t001 = resolved(&t001_source);
    let ResolvedDefinitionKind::Equational(t001_definition) = &t001.definitions[0].kind else {
        panic!("expected equational definition")
    };
    let error = run_source(t001_source).expect_err("definition result should fail");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected source typing diagnostic")
    };
    assert_eq!(diagnostic.reason, TypeReason::DefinitionResult);
    assert_eq!(
        diagnostic.primary.span(),
        t001_definition.equation.body.span
    );
    let (_, codomain) = t001_definition
        .interface
        .annotation
        .provenance
        .function_parts()
        .expect("expected function annotation");
    assert_eq!(diagnostic.related[0].span(), codomain.span().unwrap());

    let t004_source = SourceFile::new(
        "t004.ash",
        "identity : Int -> Int\nidentity value = value\n\nidentity true\n",
    )
    .expect("test source should fit");
    let t004 = resolved(&t004_source);
    let ResolvedDefinitionKind::Equational(t004_definition) = &t004.definitions[0].kind else {
        panic!("expected equational definition")
    };
    let ash::resolved::ResolvedExprKind::Apply(application) = &t004.result.kind else {
        panic!("expected application")
    };
    let error = run_source(t004_source).expect_err("argument should fail");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected source typing diagnostic")
    };
    assert_eq!(diagnostic.reason, TypeReason::Argument);
    assert_eq!(diagnostic.primary.span(), application.argument.span);
    let (domain, _) = t004_definition
        .interface
        .annotation
        .provenance
        .function_parts()
        .expect("expected function annotation");
    assert_eq!(diagnostic.related[0].span(), domain.span().unwrap());

    let operational_source = SourceFile::new(
        "t004-operational.ash",
        "fn identity(value : Int) -> Int {\n    value\n}\n\nidentity true\n",
    )
    .expect("test source should fit");
    let operational = resolved(&operational_source);
    let ResolvedDefinitionKind::InlineOperational(operational_definition) =
        &operational.definitions[0].kind
    else {
        panic!("expected operational definition")
    };
    let ash::resolved::ResolvedExprKind::Apply(application) = &operational.result.kind else {
        panic!("expected application")
    };
    let error = run_source(operational_source).expect_err("argument should fail");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected source typing diagnostic")
    };
    assert_eq!(diagnostic.reason, TypeReason::Argument);
    assert_eq!(diagnostic.primary.span(), application.argument.span);
    assert_eq!(
        diagnostic.related[0].span(),
        operational_definition.header.parameter.annotation.span
    );
}
