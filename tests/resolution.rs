use ash::{
    lexer::lex,
    parser::{STRUCTURAL_DEPTH_LIMIT, parse, project},
    resolve::{ResolveReason, resolve},
    resolved::{
        ResolvedBinding, ResolvedBlock, ResolvedDefinitionKind, ResolvedExprKind,
        ResolvedLocalDeclaration,
    },
    source::SourceFile,
    surface::SurfaceTypeKind,
};

fn resolve_valid(text: &str) -> ash::resolved::ResolvedProgram {
    let source = SourceFile::new("resolution.ash", text).expect("the fixture should fit");
    let lexed = lex(&source).expect("the fixture should lex");
    assert!(lexed.diagnostics.is_empty());
    let tree = parse(lexed);
    let surface = project(&source, &tree).expect("the fixture should project");
    resolve(&surface).expect("the fixture should resolve")
}

fn resolve_error(text: &str) -> ash::resolve::ResolveError {
    let source = SourceFile::new("resolution.ash", text).expect("the fixture should fit");
    let lexed = lex(&source).expect("the fixture should lex");
    assert!(lexed.diagnostics.is_empty());
    let tree = parse(lexed);
    let surface = project(&source, &tree).expect("the fixture should project");
    resolve(&surface).expect_err("the fixture should fail resolution")
}

fn binding(block: &ResolvedBlock, index: usize) -> &ResolvedBinding {
    let ResolvedLocalDeclaration::Binding(binding) = &block.declarations[index];
    binding
}

#[test]
fn completed_global_is_visible_to_the_program_result() {
    let program = resolve_valid("identity : Int -> Int\nidentity value = value\n\nidentity 1\n");

    let ResolvedDefinitionKind::Equational(definition) = &program.definitions[0].kind else {
        panic!("expected an equational definition");
    };
    let ResolvedExprKind::Apply(application) = &program.result.kind else {
        panic!("expected an application");
    };
    let ResolvedExprKind::Occurrence(global_use) = &application.function.kind else {
        panic!("expected a resolved global occurrence");
    };

    assert_eq!(global_use.binder, definition.interface.name.id);
    assert_eq!(
        definition.equation.name.binder,
        definition.interface.name.id
    );
    assert_eq!(global_use.spelling, "identity");
}

#[test]
fn equation_name_mismatch_relates_the_equation_head_to_the_interface() {
    let error = resolve_error("first : Int -> Int\nsecond value = value\n\nfirst\n");

    assert_eq!(error.reason, ResolveReason::EquationNameMismatch);
    assert_eq!(error.primary.span().range().start(), 19);
    assert_eq!(error.primary.span().range().end(), 25);
    assert_eq!(error.related.len(), 1);
    assert_eq!(error.related[0].span().range().start(), 0);
    assert_eq!(error.related[0].span().range().end(), 5);
    assert_eq!(error.expected.as_deref(), Some("first"));
    assert_eq!(error.found.as_deref(), Some("second"));
}

#[test]
fn duplicate_global_relates_the_second_name_to_the_first_name_and_definition() {
    let error = resolve_error(
        "same : Int -> Int\nsame value = value\n\nsame : Int -> Int\nsame other = other\n\nsame\n",
    );

    assert_eq!(error.reason, ResolveReason::DuplicateGlobal);
    assert_eq!(error.primary.span().range().start(), 38);
    assert_eq!(error.primary.span().range().end(), 42);
    assert_eq!(error.related.len(), 2);
    assert_eq!(error.related[0].span().range().start(), 0);
    assert_eq!(error.related[0].span().range().end(), 4);
    assert_eq!(error.related[1].span().range().start(), 0);
    assert_eq!(error.related[1].span().range().end(), 36);
}

#[test]
fn inline_operational_global_resolves_parameter_and_later_global_use() {
    let program = resolve_valid("fn identity(value : Int) -> Int {\n    value\n}\n\nidentity 1\n");

    let ResolvedDefinitionKind::InlineOperational(definition) = &program.definitions[0].kind else {
        panic!("expected an inline operational definition");
    };
    let ResolvedExprKind::Occurrence(body_use) = &definition.body.result.kind else {
        panic!("expected a resolved parameter occurrence");
    };
    let ResolvedExprKind::Apply(application) = &program.result.kind else {
        panic!("expected an application");
    };
    let ResolvedExprKind::Occurrence(global_use) = &application.function.kind else {
        panic!("expected a resolved global occurrence");
    };

    assert_eq!(body_use.binder, definition.header.parameter.binder.id);
    assert_eq!(global_use.binder, definition.header.name.id);
    assert_ne!(body_use.binder, global_use.binder);
}

#[test]
fn local_initializer_uses_incoming_scope_before_shadowing_binder_is_introduced() {
    let program = resolve_valid("{\n    let value = 1\n    let value = value + 1\n    value\n}\n");
    let ResolvedExprKind::Block(block) = &program.result.kind else {
        panic!("expected a resolved block");
    };
    let first = &binding(block, 0).binder;
    let second = &binding(block, 1).binder;
    let ResolvedExprKind::Add(addition) = &binding(block, 1).initializer.kind else {
        panic!("expected an addition initializer");
    };
    let ResolvedExprKind::Occurrence(initializer_use) = &addition.left.kind else {
        panic!("expected a resolved initializer occurrence");
    };
    let ResolvedExprKind::Occurrence(result_use) = &block.result.kind else {
        panic!("expected a resolved result occurrence");
    };

    assert_ne!(first.id, second.id);
    assert_eq!(initializer_use.binder, first.id);
    assert_eq!(result_use.binder, second.id);
    assert_eq!(first.origin.primary_span().range().start(), 10);
    assert_eq!(second.origin.primary_span().range().start(), 28);
    assert_eq!(initializer_use.origin.primary_span().range().start(), 36);
    assert_eq!(result_use.origin.primary_span().range().start(), 50);
}

#[test]
fn anonymous_parameter_shadows_outer_binder_only_inside_its_body() {
    let program = resolve_valid(
        "{\n    let value = 1\n    let identity = fn(value) {\n        value\n    }\n    value\n}\n",
    );
    let ResolvedExprKind::Block(block) = &program.result.kind else {
        panic!("expected a resolved block");
    };
    let outer = &binding(block, 0).binder;
    let ResolvedExprKind::Function(function) = &binding(block, 1).initializer.kind else {
        panic!("expected a resolved anonymous function");
    };
    let ResolvedExprKind::Occurrence(body_use) = &function.body.result.kind else {
        panic!("expected a resolved parameter occurrence");
    };
    let ResolvedExprKind::Occurrence(block_use) = &block.result.kind else {
        panic!("expected a resolved outer occurrence");
    };

    assert_ne!(outer.id, function.parameter.id);
    assert_eq!(body_use.binder, function.parameter.id);
    assert_eq!(block_use.binder, outer.id);
}

#[test]
fn primitive_and_binary_forms_preserve_values_and_operator_spans() {
    let boolean = resolve_valid("true == (2 * 3 + 4)\n");
    let ResolvedExprKind::Equal(equality) = &boolean.result.kind else {
        panic!("expected equality");
    };
    assert!(matches!(
        equality.left.kind,
        ResolvedExprKind::Boolean(true)
    ));
    assert_eq!(equality.operator_span.range().start(), 5);
    let ResolvedExprKind::Add(addition) = &equality.right.kind else {
        panic!("expected addition");
    };
    let ResolvedExprKind::Multiply(multiplication) = &addition.left.kind else {
        panic!("expected multiplication");
    };
    assert_eq!(multiplication.operator_span.range().start(), 11);
    assert_eq!(addition.operator_span.range().start(), 15);

    let unit = resolve_valid("()\n");
    assert!(matches!(unit.result.kind, ResolvedExprKind::Unit));
}

#[test]
fn unknown_name_has_r001_reason_and_only_the_causal_occurrence() {
    let error = resolve_error("missing\n");

    assert_eq!(error.reason, ResolveReason::UnknownName);
    assert_eq!(error.reason.to_string(), "resolve.unknown-name");
    assert_eq!(error.primary.span().range().start(), 0);
    assert_eq!(error.primary.span().range().end(), 7);
    assert!(error.related.is_empty());
    assert!(error.expected.is_none());
    assert!(error.found.is_none());
    assert!(error.help.is_none());
}

#[test]
fn global_body_cannot_see_itself_or_a_later_global() {
    let recursive = resolve_error("self : Int -> Int\nself value = self value\n\nself\n");
    assert_eq!(recursive.reason, ResolveReason::UnknownName);
    assert_eq!(recursive.primary.span().range().start(), 31);
    assert_eq!(recursive.primary.span().range().end(), 35);

    let forward = resolve_error(
        "first : Int -> Int\nfirst value = second value\n\nsecond : Int -> Int\nsecond value = value\n\nfirst\n",
    );
    assert_eq!(forward.reason, ResolveReason::UnknownName);
    assert_eq!(forward.primary.span().range().start(), 33);
    assert_eq!(forward.primary.span().range().end(), 39);
}

#[test]
fn later_global_body_resolves_an_earlier_global_identity() {
    let program = resolve_valid(
        "first : Int -> Int\nfirst value = value\n\nsecond : Int -> Int\nsecond value = first value\n\nsecond 1\n",
    );
    let ResolvedDefinitionKind::Equational(first) = &program.definitions[0].kind else {
        panic!("expected first equation");
    };
    let ResolvedDefinitionKind::Equational(second) = &program.definitions[1].kind else {
        panic!("expected second equation");
    };
    let ResolvedExprKind::Apply(application) = &second.equation.body.kind else {
        panic!("expected the second body application");
    };
    let ResolvedExprKind::Occurrence(first_use) = &application.function.kind else {
        panic!("expected an earlier-global occurrence");
    };

    assert_eq!(first_use.binder, first.interface.name.id);
    assert_ne!(first_use.binder, second.interface.name.id);
}

#[test]
fn local_initializer_cannot_see_the_binder_it_is_defining() {
    let error = resolve_error("{\n    let value = value\n    value\n}\n");

    assert_eq!(error.reason, ResolveReason::UnknownName);
    assert_eq!(error.primary.span().range().start(), 18);
    assert_eq!(error.primary.span().range().end(), 23);
}

#[test]
fn duplicate_check_applies_across_both_global_presentations() {
    let error = resolve_error(
        "first : Int -> Int\nfirst value = value\n\nfn first(value : Int) -> Int {\n    value\n}\n\nfirst\n",
    );

    assert_eq!(error.reason, ResolveReason::DuplicateGlobal);
    assert_eq!(error.primary.span().range().start(), 43);
    assert_eq!(error.primary.span().range().end(), 48);
    assert_eq!(error.related.len(), 2);
}

#[test]
fn definition_and_occurrence_keep_distinct_causal_origins_and_exact_spelling() {
    let program = resolve_valid("identity : Int -> Int\nidentity value = value\n\nidentity\n");
    let ResolvedDefinitionKind::Equational(definition) = &program.definitions[0].kind else {
        panic!("expected an equation");
    };
    let ResolvedExprKind::Occurrence(use_site) = &program.result.kind else {
        panic!("expected a resolved occurrence");
    };

    assert_eq!(definition.interface.name.spelling, "identity");
    assert_eq!(use_site.spelling, "identity");
    assert_eq!(use_site.binder, definition.interface.name.id);
    assert_eq!(
        definition
            .interface
            .name
            .origin
            .primary_span()
            .range()
            .start(),
        0
    );
    assert_eq!(
        definition
            .interface
            .name
            .origin
            .primary_span()
            .range()
            .end(),
        8
    );
    assert_eq!(use_site.origin.primary_span().range().start(), 46);
    assert_eq!(use_site.origin.primary_span().range().end(), 54);
}

#[test]
fn admitted_expression_depth_resolves_and_drops_on_a_small_host_stack() {
    let expression = std::iter::repeat_n("1", STRUCTURAL_DEPTH_LIMIT + 1)
        .collect::<Vec<_>>()
        .join(" + ");
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let program = resolve_valid(&expression);
            assert!(matches!(program.result.kind, ResolvedExprKind::Add(_)));
        })
        .expect("the depth-test worker should start");

    worker
        .join()
        .expect("resolution and recursive value drop should remain within the stack budget");
}

#[test]
fn admitted_function_and_block_depth_resolves_and_drops_on_a_small_host_stack() {
    let mut expression = "1".to_owned();
    for _ in 0..(STRUCTURAL_DEPTH_LIMIT / 2) {
        expression = format!("fn(value) {{\n{expression}\n}}");
    }
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let program = resolve_valid(&expression);
            assert!(matches!(program.result.kind, ResolvedExprKind::Function(_)));
        })
        .expect("the nested-function worker should start");

    worker
        .join()
        .expect("nested function resolution and drop should remain within the stack budget");
}

#[test]
fn admitted_type_depth_resolves_and_drops_on_a_small_host_stack() {
    let source = format!(
        "f : {}Int\nf value = value\n\nf\n",
        "Int -> ".repeat(STRUCTURAL_DEPTH_LIMIT)
    );
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let program = resolve_valid(&source);
            assert_eq!(program.definitions.len(), 1);
        })
        .expect("the nested-type worker should start");

    worker
        .join()
        .expect("type preservation and drop should remain within the stack budget");
}

#[test]
fn resolved_presentations_retain_annotations_component_spans_and_full_spans() {
    let program = resolve_valid(
        "fn increment(value : Int) -> Int {\n    let one : Int = 1\n    value + one\n}\n\nincrement 41\n",
    );
    let definition = &program.definitions[0];
    let ResolvedDefinitionKind::InlineOperational(definition) = &definition.kind else {
        panic!("expected an inline operational definition");
    };

    assert_eq!(
        definition.header.name.origin.primary_span().range().start(),
        3
    );
    assert_eq!(definition.header.parameter.span.range().start(), 13);
    assert_eq!(definition.header.parameter.span.range().end(), 24);
    assert!(matches!(
        definition.header.parameter.annotation.kind,
        SurfaceTypeKind::Int
    ));
    assert_eq!(definition.header.result_type.span.range().start(), 29);
    assert_eq!(definition.header.result_type.span.range().end(), 32);
    assert_eq!(binding(&definition.body, 0).span.range().start(), 39);
    assert_eq!(binding(&definition.body, 0).span.range().end(), 56);
    assert!(matches!(
        binding(&definition.body, 0)
            .annotation
            .as_ref()
            .map(|annotation| &annotation.kind),
        Some(SurfaceTypeKind::Int)
    ));
    let ResolvedExprKind::Add(addition) = &definition.body.result.kind else {
        panic!("expected an addition body");
    };
    assert_eq!(addition.operator_span.range().start(), 67);
    assert_eq!(addition.operator_span.range().end(), 68);
    assert_eq!(definition.body.span.range().start(), 33);
    assert_eq!(definition.body.span.range().end(), 74);
    assert_eq!(program.span.range().start(), 0);
    assert_eq!(program.span.range().end(), 89);
}

#[test]
fn fail_fast_resolution_reports_only_the_first_unavailable_name_fact() {
    let error = resolve_error("missing + unavailable\n");

    assert_eq!(error.reason, ResolveReason::UnknownName);
    assert_eq!(error.primary.span().range().start(), 0);
    assert_eq!(error.primary.span().range().end(), 7);
    assert!(error.related.is_empty());
}

#[test]
fn local_binding_may_shadow_a_global_without_changing_the_global_identity() {
    let program = resolve_valid(
        "value : Int -> Int\nvalue parameter = parameter\n\n{\n    let value = 1\n    value\n}\n",
    );
    let ResolvedDefinitionKind::Equational(global) = &program.definitions[0].kind else {
        panic!("expected an equation");
    };
    let ResolvedExprKind::Block(block) = &program.result.kind else {
        panic!("expected a block");
    };
    let ResolvedExprKind::Occurrence(local_use) = &block.result.kind else {
        panic!("expected a local occurrence");
    };

    assert_ne!(binding(block, 0).binder.id, global.interface.name.id);
    assert_eq!(local_use.binder, binding(block, 0).binder.id);
}

#[test]
fn anonymous_function_captures_outer_binder_and_keeps_parameter_identity_separate() {
    let program = resolve_valid(
        "{\n    let offset = 40\n    let add_offset = fn(value) {\n        value + offset\n    }\n    add_offset 2\n}\n",
    );
    let ResolvedExprKind::Block(block) = &program.result.kind else {
        panic!("expected a block");
    };
    let offset = &binding(block, 0).binder;
    let ResolvedExprKind::Function(function) = &binding(block, 1).initializer.kind else {
        panic!("expected an anonymous function");
    };
    let ResolvedExprKind::Add(addition) = &function.body.result.kind else {
        panic!("expected an addition body");
    };
    let ResolvedExprKind::Occurrence(parameter_use) = &addition.left.kind else {
        panic!("expected a parameter occurrence");
    };
    let ResolvedExprKind::Occurrence(capture_use) = &addition.right.kind else {
        panic!("expected a captured occurrence");
    };

    assert_eq!(parameter_use.binder, function.parameter.id);
    assert_eq!(capture_use.binder, offset.id);
    assert_ne!(parameter_use.binder, capture_use.binder);
}
