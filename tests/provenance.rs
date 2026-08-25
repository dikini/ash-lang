use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{PureComputation, PureExprKind, PureValue, ValidatedProgram, validate_modules},
    driver::PipelineFailure,
    elaborate::{Elaborator, TypeContext, TypeError, TypeReason, check_module, link_modules},
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    resolve::resolve_module,
    resolved::{
        Binder, ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind, ResolvedLocalDeclaration,
        ResolvedModule, ResolvedPattern, ResolvedPatternKind,
    },
    source::{GeneratedReason, Origin, SourceFile, Span},
};
static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

fn pattern_binder(pattern: &ResolvedPattern) -> &Binder {
    let ResolvedPatternKind::Binder(binder) = &pattern.kind else {
        panic!("expected binder pattern")
    };
    binder
}

fn with_graph<T>(name: &str, text: &str, action: impl FnOnce(&ash::module::ModuleGraph) -> T) -> T {
    let directory = loop {
        let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ash-provenance-module-{}-{id}", std::process::id()));
        match fs::create_dir(&path) {
            Ok(()) => break path,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("provenance fixture directory should be creatable: {error}"),
        }
    };
    let entry = directory.join(name);
    fs::write(&entry, text).expect("provenance fixture should be writable");
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("provenance fixture should load");
    let result = action(&graph);
    let _ = fs::remove_dir_all(directory);
    result
}

fn resolved(name: &str, text: &str) -> (SourceFile, ResolvedModule) {
    with_graph(name, text, |graph| {
        let source = graph.modules()[0].source().clone();
        let resolved = resolve_module(&graph.modules()[0], &[]).expect("fixture should resolve");
        (source, resolved)
    })
}

fn resolved_typing_error(name: &str, text: &str) -> (ResolvedModule, PipelineFailure) {
    with_graph(name, text, |graph| {
        let inspection = resolve_module(&graph.modules()[0], &[]).expect("fixture should resolve");
        let error = check_module(
            resolve_module(&graph.modules()[0], &[]).expect("fixture should resolve again"),
        )
        .expect_err("fixture should fail checking");
        (inspection, PipelineFailure::Typing(error))
    })
}

fn validated_entry_body(
    source: &SourceFile,
    module: &ResolvedModule,
    expression: &ResolvedExpr,
) -> ValidatedProgram {
    let mut elaborator = Elaborator::for_resolved_expression(module, expression)
        .expect("binder namespace should fit");
    let typed = elaborator
        .synthesize(expression, &TypeContext::new())
        .expect("test program should elaborate");
    validate_modules(
        elaborator.finish(typed.node).expect("root should finish"),
        &[source],
        &[(module.module(), source.id())],
    )
    .expect("elaborated Core should validate")
}

fn validated_module(name: &str, text: &str) -> (SourceFile, ResolvedModule, ValidatedProgram) {
    with_graph(name, text, |graph| {
        let source = graph.modules()[0].source().clone();
        let inspection = resolve_module(&graph.modules()[0], &[]).expect("fixture should resolve");
        let checked = check_module(
            resolve_module(&graph.modules()[0], &[]).expect("fixture should resolve again"),
        )
        .expect("fixture should check");
        let linked = link_modules(vec![checked], graph.entry()).expect("fixture should link");
        let linked = validate_interface_evidence(linked).expect("linked evidence should validate");
        let mut elaborator =
            Elaborator::for_module_program(&linked).expect("binder namespace should fit");
        let typed = elaborator
            .synthesize_module_program(&linked)
            .expect("fixture should elaborate");
        let unchecked = elaborator.finish(typed.node).expect("root should finish");
        let validated = validate_modules(unchecked, &[&source], &[(graph.entry(), source.id())])
            .expect("Core should validate");
        (source, inspection, validated)
    })
}

fn main_body(module: &ResolvedModule) -> &ResolvedExpr {
    module
        .definitions()
        .iter()
        .find_map(|definition| match &definition.kind {
            ResolvedDefinitionKind::Equational(global)
                if global.interface.name.spelling == "main" =>
            {
                Some(&global.equations[0].body)
            }
            _ => None,
        })
        .expect("fixture should declare equational main")
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
    let (source, program) = resolved(
        "recursive-origins.ash",
        "main : Unit -> Int\nmain () = {\nlet rec repeat : Unit -> Int = fn(ignored) {\nrepeat ()\n}\nrepeat ()\n}\n",
    );
    let ResolvedExprKind::Block(block) = &main_body(&program).kind else {
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

    let core = validated_entry_body(&source, &program, main_body(&program));
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
        pattern_binder(&source_function.pattern)
            .origin
            .primary_span()
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
            "increment : Int -> Int\nincrement value = value + 1\n\nmain : Unit -> Int\nmain () = increment 41\n",
        ),
        (
            "operational.ash",
            "fn increment(value : Int) -> Int {\n    value + 1\n}\n\nmain : Unit -> Int\nmain () = increment 41\n",
        ),
    ] {
        let (_source, program, core) = validated_module(path, text);
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

        match &program.definitions()[0].kind {
            ResolvedDefinitionKind::Equational(definition) => assert_check_origin(
                &body.origin,
                definition.equations[0].body.span,
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
            "increment : Int -> Int\nincrement value = value + 1\n\nmain : Unit -> Int\nmain () = increment 41\n",
        ),
        (
            "operational-causes.ash",
            "fn increment(value : Int) -> Int {\n    value + 1\n}\n\nmain : Unit -> Int\nmain () = increment 41\n",
        ),
    ] {
        let (_source, program, core) = validated_module(path, text);
        let definition = &program.definitions()[0];
        let root = core.node(core.root()).expect("global binding");
        let PureExprKind::Computation(PureComputation::RecursiveBind(global)) = &root.kind else {
            panic!("expected global recursive group")
        };
        assert_eq!(
            root.origin.generated_reason(),
            Some(GeneratedReason::RecursiveBindingLowering)
        );
        assert_eq!(root.origin.primary_span(), program.span());

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
                assert_eq!(function.origin.primary_span(), equational.equations[0].span);
                for expected in [
                    definition.span,
                    equational.interface.span,
                    equational.interface.annotation.span,
                    equational.equations[0].body.span,
                ] {
                    assert!(function.origin.related_spans().contains(&expected));
                }
                assert_eq!(
                    function_node.parameter().origin().primary_span(),
                    pattern_binder(&equational.equations[0].patterns[0])
                        .origin
                        .primary_span()
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
                    operational.header.parameters[0].annotation.span,
                    operational.header.result_type.span,
                    operational.body.span,
                ] {
                    assert!(function.origin.related_spans().contains(&expected));
                }
                assert_eq!(
                    function_node.parameter().origin().primary_span(),
                    pattern_binder(&operational.header.parameters[0].pattern)
                        .origin
                        .primary_span()
                );
            }
        }

        let source_result = main_body(&program);
        let ash::resolved::ResolvedExprKind::Apply(resolved_application) = &source_result.kind
        else {
            panic!("expected resolved application")
        };
        let mut pending = vec![
            global
                .members()
                .last()
                .expect("main should be the final global")
                .initializer(),
        ];
        let (application, application_node) = loop {
            let node = core
                .node(
                    pending
                        .pop()
                        .expect("main Core should contain its application"),
                )
                .expect("main Core node should exist");
            if node.origin.primary_span() == source_result.span
                && let PureExprKind::Computation(PureComputation::Apply(application)) = &node.kind
            {
                break (node, application);
            }
            for index in 0..node.kind.child_count() {
                pending.push(node.kind.child_at(index).expect("Core child should exist"));
            }
        };
        let ResolvedDefinitionKind::Equational(main) =
            &program.definitions().last().expect("main definition").kind
        else {
            panic!("main should be equational")
        };
        let (_, main_result) = main
            .interface
            .annotation
            .provenance
            .function_parts()
            .expect("main should have a function type");
        assert_check_origin(
            &application.origin,
            source_result.span,
            main_result.span().expect("main result should have a span"),
        );
        assert_eq!(
            resolved_application.function.span.source(),
            source_result.span.source()
        );
        assert_eq!(
            resolved_application.argument.span.source(),
            source_result.span.source()
        );
        assert!(core.node(application_node.function()).is_some());
        assert!(core.node(application_node.argument()).is_some());
    }
}

#[test]
fn t001_and_t004_diagnostics_keep_their_source_cause_spans() {
    let t001_text =
        "wrong : Int -> Bool\nwrong value = value\n\nmain : Unit -> Bool\nmain () = true\n";
    let (t001, error) = resolved_typing_error("t001.ash", t001_text);
    let ResolvedDefinitionKind::Equational(t001_definition) = &t001.definitions()[0].kind else {
        panic!("expected equational definition")
    };
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected source typing diagnostic")
    };
    assert_eq!(diagnostic.reason, TypeReason::DefinitionResult);
    assert_eq!(
        diagnostic.primary.span(),
        t001_definition.equations[0].body.span
    );
    let (_, codomain) = t001_definition
        .interface
        .annotation
        .provenance
        .function_parts()
        .expect("expected function annotation");
    assert_eq!(diagnostic.related[0].span(), codomain.span().unwrap());

    let t004_text = "identity : Int -> Int\nidentity value = value\n\nmain : Unit -> Int\nmain () = identity true\n";
    let (t004, error) = resolved_typing_error("t004.ash", t004_text);
    let ResolvedDefinitionKind::Equational(t004_definition) = &t004.definitions()[0].kind else {
        panic!("expected equational definition")
    };
    let ash::resolved::ResolvedExprKind::Apply(application) = &main_body(&t004).kind else {
        panic!("expected application")
    };
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

    let operational_text = "fn identity(value : Int) -> Int {\n    value\n}\n\nmain : Unit -> Int\nmain () = identity true\n";
    let (operational, error) = resolved_typing_error("t004-operational.ash", operational_text);
    let ResolvedDefinitionKind::InlineOperational(operational_definition) =
        &operational.definitions()[0].kind
    else {
        panic!("expected operational definition")
    };
    let ash::resolved::ResolvedExprKind::Apply(application) = &main_body(&operational).kind else {
        panic!("expected application")
    };
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected source typing diagnostic")
    };
    assert_eq!(diagnostic.reason, TypeReason::Argument);
    assert_eq!(diagnostic.primary.span(), application.argument.span);
    assert_eq!(
        diagnostic.related[0].span(),
        operational_definition.header.parameters[0].annotation.span
    );
}
