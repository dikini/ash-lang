use std::{
    collections::HashSet,
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{
        EffectExprKind, EffectOperation, EffectOperationFamily, NodeId, PureComputation,
        PureExprKind, ValidatedEffectProgram, dialect::CoreOperationFamily,
        validate_effect_modules,
    },
    driver::PipelineFailure,
    elaborate::{EffectElaborator, TypeError, TypeReason, check_module, link_modules},
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{
        Binder, CheckedModule, ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind,
        ResolvedLocalDeclaration, ResolvedModule, ResolvedPattern, ResolvedPatternKind,
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

fn resolve_entry(graph: &ash::module::ModuleGraph) -> (ResolvedModule, Vec<CheckedModule>) {
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency| dependency.module() == edge.target())
                    .expect("dependency should precede importer");
                DependencyExports::new(edge, dependency.exports())
                    .expect("exact target summary should authenticate")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies).expect("fixture should resolve");
        if module.id() == graph.entry() {
            return (resolved, checked);
        }
        checked.push(check_module(resolved).expect("dependency should check"));
    }
    panic!("entry should belong to graph")
}

fn resolved_typing_error(name: &str, text: &str) -> (ResolvedModule, PipelineFailure) {
    with_graph(name, text, |graph| {
        let (inspection, _) = resolve_entry(graph);
        let (target, _) = resolve_entry(graph);
        let error = check_module(target).expect_err("fixture should fail checking");
        (inspection, PipelineFailure::Typing(error))
    })
}

fn validated_module(
    name: &str,
    text: &str,
) -> (SourceFile, ResolvedModule, ValidatedEffectProgram) {
    with_graph(name, text, |graph| {
        let source = graph.module(graph.entry()).unwrap().source().clone();
        let (inspection, _) = resolve_entry(graph);
        let (target, mut checked) = resolve_entry(graph);
        checked.push(check_module(target).expect("entry should check"));
        let linked = link_modules(checked, graph.entry()).expect("fixture should link");
        let linked = validate_interface_evidence(linked).expect("linked evidence should validate");
        let mut elaborator =
            EffectElaborator::for_module_program(&linked).expect("binder namespace should fit");
        let typed = elaborator
            .synthesize_effect_module_program(&linked)
            .expect("fixture should elaborate");
        let unchecked = elaborator.finish(typed.node).expect("root should finish");
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
        let validated = validate_effect_modules(unchecked, &sources, &module_sources)
            .expect("Core should validate");
        (source, inspection, validated)
    })
}

fn owned_nodes(core: &ValidatedEffectProgram, root: NodeId) -> Vec<NodeId> {
    let mut pending = vec![root];
    let mut seen = HashSet::new();
    let mut nodes = Vec::new();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        let node = core.node(id).unwrap();
        pending
            .extend((0..node.kind.child_count()).map(|index| node.kind.child_at(index).unwrap()));
        nodes.push(id);
    }
    nodes
}

fn core_source_group(core: &ValidatedEffectProgram, binder: ash::resolved::BinderId) -> NodeId {
    let groups = owned_nodes(core, core.root()).into_iter().filter(|id| {
        matches!(&core.node(*id).unwrap().kind, EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(group)))
            if group.members().iter().any(|member| member.binder().id() == binder))
    }).collect::<Vec<_>>();
    let [group] = groups.as_slice() else {
        panic!("source binder should own one recursive group")
    };
    *group
}

fn source_closure(core: &ValidatedEffectProgram, initializer: NodeId, span: Span) -> NodeId {
    let closures = owned_nodes(core, initializer)
        .into_iter()
        .filter(|id| {
            let node = core.node(*id).unwrap();
            node.origin.primary_span() == span
                && matches!(
                    node.kind,
                    EffectExprKind::Operation(EffectOperation::RegionClosure(_))
                )
        })
        .collect::<Vec<_>>();
    let [closure] = closures.as_slice() else {
        panic!("source initializer should own one closure at its exact function span")
    };
    assert_eq!(
        core.node(*closure).unwrap().ty,
        core.node(initializer).unwrap().ty
    );
    assert!(core.node(*closure).unwrap().ty.function_view().is_some());
    *closure
}

fn parameter(core: &ValidatedEffectProgram, closure: NodeId) -> ash::core::TypedBinder {
    let mut parameters = Vec::new();
    EffectOperationFamily::visit_operation_binders(
        &core.node(closure).unwrap().kind,
        &mut |parameter| parameters.push(parameter.clone()),
    );
    let [parameter] = parameters.as_slice() else {
        panic!("source closure should have one parameter")
    };
    assert_eq!(
        parameter.ty(),
        core.node(closure)
            .unwrap()
            .ty
            .function_view()
            .unwrap()
            .domain()
    );
    parameter.clone()
}

fn main_body(module: &ResolvedModule) -> &ResolvedExpr {
    module
        .definitions()
        .iter()
        .find_map(|definition| match &definition.kind {
            ResolvedDefinitionKind::Equational(global)
            | ResolvedDefinitionKind::ForeignConstant(global)
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
    let (_source, program, core) = validated_module(
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

    let root = core
        .node(core_source_group(&core, source_member.binder.id))
        .expect("recursive root");
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(group))) =
        &root.kind
    else {
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

    let closure = source_closure(
        &core,
        group.members()[0].initializer(),
        source_member.initializer.span,
    );
    let function = core.node(closure).unwrap();
    assert_eq!(
        function.origin.primary_span(),
        source_member.initializer.span
    );
    assert_eq!(
        parameter(&core, closure).origin().primary_span(),
        pattern_binder(&source_function.pattern)
            .origin
            .primary_span()
    );
    let calls = owned_nodes(&core, closure)
        .into_iter()
        .filter(|id| {
            let node = core.node(*id).unwrap();
            node.origin.primary_span() == source_function.body.result.span
                && matches!(
                    node.kind,
                    EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(_)))
                )
        })
        .collect::<Vec<_>>();
    let [body] = calls.as_slice() else {
        panic!("one owned recursive source application")
    };
    let body = core.node(*body).unwrap();
    assert_eq!(body.origin.primary_span(), source_function.body.result.span);
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(call))) = &body.kind
    else {
        unreachable!()
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
        let binder = match &program.definitions()[0].kind {
            ResolvedDefinitionKind::Equational(global)
            | ResolvedDefinitionKind::ForeignConstant(global) => global.interface.name.id,
            ResolvedDefinitionKind::InlineOperational(global) => global.header.name.id,
        };
        let root = core
            .node(core_source_group(&core, binder))
            .expect("global binding");
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(global))) =
            &root.kind
        else {
            panic!("expected global recursive group")
        };
        let member = global
            .members()
            .iter()
            .find(|member| member.binder().id() == binder)
            .expect("original source member");
        let function_span = match &program.definitions()[0].kind {
            ResolvedDefinitionKind::Equational(global)
            | ResolvedDefinitionKind::ForeignConstant(global) => global.equations[0].span,
            ResolvedDefinitionKind::InlineOperational(_) => program.definitions()[0].span,
        };
        let closure = source_closure(&core, member.initializer(), function_span);

        let body_span = match &program.definitions()[0].kind {
            ResolvedDefinitionKind::Equational(global)
            | ResolvedDefinitionKind::ForeignConstant(global) => global.equations[0].body.span,
            ResolvedDefinitionKind::InlineOperational(global) => global.body.result.span,
        };
        // initialize_region_buffer returns the context binding around the buffer;
        // successful checking records its cause on that returned expression.
        let bodies = owned_nodes(&core, closure)
            .into_iter()
            .filter(|id| {
                let node = core.node(*id).unwrap();
                node.origin.primary_span() == body_span
                    && matches!(
                        node.kind,
                        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(_)))
                    )
            })
            .collect::<Vec<_>>();
        let [body] = bodies.as_slice() else {
            panic!("one owned checked arithmetic expression")
        };
        let body = core.node(*body).unwrap();

        match &program.definitions()[0].kind {
            ResolvedDefinitionKind::Equational(definition)
            | ResolvedDefinitionKind::ForeignConstant(definition) => assert_check_origin(
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
        let binder = match &program.definitions()[0].kind {
            ResolvedDefinitionKind::Equational(global)
            | ResolvedDefinitionKind::ForeignConstant(global) => global.interface.name.id,
            ResolvedDefinitionKind::InlineOperational(global) => global.header.name.id,
        };
        let root = core
            .node(core_source_group(&core, binder))
            .expect("global binding");
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(global))) =
            &root.kind
        else {
            panic!("expected global recursive group")
        };
        assert_eq!(
            root.origin.generated_reason(),
            Some(GeneratedReason::RecursiveBindingLowering)
        );
        assert_eq!(root.origin.primary_span(), program.span());

        let member = global
            .members()
            .iter()
            .find(|member| member.binder().id() == binder)
            .expect("original source member");
        let function_span = match &program.definitions()[0].kind {
            ResolvedDefinitionKind::Equational(global)
            | ResolvedDefinitionKind::ForeignConstant(global) => global.equations[0].span,
            ResolvedDefinitionKind::InlineOperational(_) => program.definitions()[0].span,
        };
        let closure = source_closure(&core, member.initializer(), function_span);
        let function = core.node(closure).unwrap();
        let function_parameter = parameter(&core, closure);
        assert_eq!(
            function.origin.generated_reason(),
            Some(GeneratedReason::FunctionLowering)
        );
        assert_eq!(
            function_parameter.origin().generated_reason(),
            Some(GeneratedReason::FunctionLowering)
        );

        match &definition.kind {
            ResolvedDefinitionKind::Equational(equational)
            | ResolvedDefinitionKind::ForeignConstant(equational) => {
                assert_eq!(member.binder().id(), equational.interface.name.id);
                assert_eq!(
                    member.binder().origin().primary_span(),
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
                    function_parameter.origin().primary_span(),
                    pattern_binder(&equational.equations[0].patterns[0])
                        .origin
                        .primary_span()
                );
            }
            ResolvedDefinitionKind::InlineOperational(operational) => {
                assert_eq!(member.binder().id(), operational.header.name.id);
                assert_eq!(
                    member.binder().origin().primary_span(),
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
                    function_parameter.origin().primary_span(),
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
        let main = program
            .definitions()
            .iter()
            .find_map(|definition| match &definition.kind {
                ResolvedDefinitionKind::Equational(main)
                    if main.interface.name.spelling == "main" =>
                {
                    Some(main)
                }
                _ => None,
            })
            .expect("main should be equational");
        let main_initializer = global
            .members()
            .iter()
            .find(|member| member.binder().id() == main.interface.name.id)
            .expect("main binder owns an initializer")
            .initializer();
        let applications = owned_nodes(&core, main_initializer)
            .into_iter()
            .filter(|id| {
                let node = core.node(*id).unwrap();
                node.origin.primary_span() == source_result.span
                    && matches!(
                        node.kind,
                        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(_)))
                    )
            })
            .collect::<Vec<_>>();
        let [application] = applications.as_slice() else {
            panic!("one source-owned main application")
        };
        let application = core.node(*application).unwrap();
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
            application_node,
        ))) = &application.kind
        else {
            unreachable!()
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
