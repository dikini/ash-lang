use ash::{
    driver::{PipelineFailure, run_source},
    elaborate::{TypeError, TypeReason},
    lexer::lex,
    parser::{ParseContext, ParseReason, ProjectionError, SynchronizationBoundary, parse, project},
    resolve::{ResolveReason, resolve},
    resolved::{ResolvedBinding, ResolvedBlock, ResolvedExprKind, ResolvedLocalDeclaration},
    source::SourceFile,
};

const P001: &str = include_str!("fixtures/first-stratum/parse/p001-missing-result.ash");
const P002: &str = include_str!("fixtures/first-stratum/parse/p002-unclosed-group.ash");
const P003: &str = include_str!("fixtures/first-stratum/parse/p003-independent-recovery.ash");
const R001: &str = include_str!("fixtures/first-stratum/resolve/r001-unknown-name.ash");
const R002: &str = include_str!("fixtures/first-stratum/resolve/r002-duplicate-global.ash");
const EQUATION_NAME_MISMATCH: &str =
    include_str!("fixtures/first-stratum/resolve/equation-name-mismatch.ash");
const T001: &str = include_str!("fixtures/first-stratum/type/t001-definition-result.ash");
const T002: &str = include_str!("fixtures/first-stratum/type/t002-operator-operand.ash");
const T003: &str = include_str!("fixtures/first-stratum/type/t003-not-applicable.ash");
const T004: &str = include_str!("fixtures/first-stratum/type/t004-argument.ash");
const EQUATION_INTERFACE_NOT_FUNCTION: &str =
    include_str!("fixtures/first-stratum/type/equation-interface-not-function.ash");
const BINDING_INITIALIZER: &str =
    include_str!("fixtures/first-stratum/type/binding-initializer.ash");
const FUNCTION_NEEDS_CONTEXT: &str =
    include_str!("fixtures/first-stratum/type/function-needs-context.ash");
const FUNCTION_RESULT_NEEDS_CONTEXT: &str =
    include_str!("fixtures/first-stratum/type/function-result-needs-context.ash");
const FUNCTION_NON_FUNCTION_CONTEXT: &str =
    include_str!("fixtures/first-stratum/type/function-non-function-context.ash");

fn source(name: &str, text: &str) -> SourceFile {
    SourceFile::new(name, text).expect("diagnostic fixture should fit the source model")
}

fn offset(value: usize) -> u32 {
    u32::try_from(value).expect("fixture offset should fit the source representation")
}

fn binding(block: &ResolvedBlock, index: usize) -> &ResolvedBinding {
    let ResolvedLocalDeclaration::Binding(binding) = &block.declarations[index] else {
        panic!("expected ordinary binding")
    };
    binding
}

#[test]
fn p001_preserves_the_complete_global_before_the_missing_result() {
    let source = source("p001.ash", P001);
    let tree = parse(lex(&source).expect("P-001 should lex"));

    assert_eq!(tree.parse_diagnostics().len(), 1);
    let diagnostic = &tree.parse_diagnostics()[0];
    assert_eq!(diagnostic.reason, ParseReason::ExpectedResult);
    assert_eq!(
        diagnostic.primary.span().range().start(),
        offset(P001.len())
    );
    assert_eq!(diagnostic.primary.span().range().end(), offset(P001.len()));
    assert_eq!(diagnostic.expected, Some("an expression".to_owned()));
    assert_eq!(diagnostic.found, Some("end of input".to_owned()));
    assert_eq!(diagnostic.related, []);
    assert_eq!(diagnostic.context.len(), 1);
    let ParseContext::PrecedingGlobalComplete {
        starting_at,
        ending_at,
        line_end,
    } = diagnostic.context[0]
    else {
        panic!("P-001 should retain the preceding global context");
    };
    assert_eq!(starting_at.range().start(), 0);
    assert_eq!(
        ending_at.range().start(),
        offset(P001.rfind('}').expect("closing brace"))
    );
    assert_eq!(line_end.range().end(), offset(P001.len()));
    assert_eq!(
        project(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn p002_labels_the_opening_group_and_the_eof_close_requirement() {
    let source = source("p002.ash", P002);
    let tree = parse(lex(&source).expect("P-002 should lex"));

    assert_eq!(tree.parse_diagnostics().len(), 1);
    let diagnostic = &tree.parse_diagnostics()[0];
    assert_eq!(diagnostic.reason, ParseReason::UnclosedGroup);
    let opening = P002.rfind('(').expect("unclosed opening parenthesis");
    assert_eq!(diagnostic.primary.span().range().start(), offset(opening));
    assert_eq!(diagnostic.primary.span().range().end(), offset(opening + 1));
    assert_eq!(diagnostic.expected, Some(")".to_owned()));
    assert_eq!(diagnostic.found, Some("end of input".to_owned()));
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(
        diagnostic.related[0].span().range().start(),
        offset(P002.len())
    );
    assert_eq!(
        project(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn p003_recovers_at_the_body_brace_then_reports_the_later_group_independently() {
    let source = source("p003.ash", P003);
    let tree = parse(lex(&source).expect("P-003 should lex"));

    assert_eq!(tree.parse_diagnostics().len(), 2);
    let operand = &tree.parse_diagnostics()[0];
    assert_eq!(operand.reason, ParseReason::ExpectedOperand);
    let operator = P003.find('+').expect("missing-operand operator");
    assert_eq!(operand.primary.span().range().start(), offset(operator));
    assert_eq!(operand.expected, Some("an operand".to_owned()));
    assert_eq!(operand.found, Some("line end".to_owned()));
    assert_eq!(operand.context.len(), 1);
    let ParseContext::Synchronization { boundary, span } = operand.context[0] else {
        panic!("P-003 should record its owning recovery boundary");
    };
    assert_eq!(boundary, SynchronizationBoundary::BlockClosingBrace);
    assert_eq!(
        span.range().start(),
        offset(P003.find('}').expect("body closing brace"))
    );
    assert_eq!(operand.related.len(), 1);
    assert_eq!(operand.related[0].span(), span);

    let group = &tree.parse_diagnostics()[1];
    assert_eq!(group.reason, ParseReason::UnclosedGroup);
    let opening = P003.rfind('(').expect("later unclosed group");
    assert_eq!(group.primary.span().range().start(), offset(opening));
    assert_eq!(group.related.len(), 1);
    assert_eq!(group.related[0].span().range().start(), offset(P003.len()));
    assert_eq!(
        project(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn r001_reports_only_the_unknown_occurrence_without_an_unjustified_suggestion() {
    let source = source("r001.ash", R001);
    let tree = parse(lex(&source).expect("R-001 should lex"));
    let surface = project(&source, &tree).expect("R-001 should project");
    let error = resolve(&surface).expect_err("R-001 should fail in resolution");

    assert_eq!(error.reason, ResolveReason::UnknownName);
    assert_eq!(error.primary.span().range().start(), 0);
    assert_eq!(error.primary.span().range().end(), offset("missing".len()));
    assert!(error.related.is_empty());
    assert!(error.expected.is_none());
    assert!(error.found.is_none());
    assert!(error.help.is_none());
}

#[test]
fn r002_relates_the_second_global_to_the_first_name_and_definition() {
    let source = source("r002.ash", R002);
    let tree = parse(lex(&source).expect("R-002 should lex"));
    let surface = project(&source, &tree).expect("R-002 should project");
    let first = &surface.definitions[0];
    let second = &surface.definitions[1];
    let error = resolve(&surface).expect_err("R-002 should fail in resolution");

    assert_eq!(error.reason, ResolveReason::DuplicateGlobal);
    assert_eq!(
        error.primary.span().range().start(),
        offset(R002.find("fn value").expect("second global") + 3)
    );
    assert_eq!(error.related.len(), 2);
    assert!(
        error
            .related
            .iter()
            .any(|label| label.span().range().start() == 0)
    );
    assert!(error.related.iter().any(|label| label.span() == first.span));
    assert_ne!(error.primary.span(), second.span);
    assert!(error.expected.is_none());
    assert!(error.found.is_none());
}

#[test]
fn equation_name_mismatch_retains_both_names_and_a_justified_correction() {
    let source = source("equation-name.ash", EQUATION_NAME_MISMATCH);
    let tree = parse(lex(&source).expect("name mismatch should lex"));
    let surface = project(&source, &tree).expect("name mismatch should project");
    let error = resolve(&surface).expect_err("the equation head should disagree");

    assert_eq!(error.reason, ResolveReason::EquationNameMismatch);
    assert_eq!(error.expected.as_deref(), Some("identity"));
    assert_eq!(error.found.as_deref(), Some("different"));
    assert_eq!(error.related.len(), 1);
    assert_eq!(error.related[0].span().range().start(), 0);
    assert_eq!(
        error.help.as_deref(),
        Some("rename the equation head to `identity`")
    );
}

#[test]
fn t001_definition_result_relates_the_body_to_the_interface_codomain() {
    let source = source("t001.ash", T001);
    let error = run_source(source).expect_err("T-001 should fail in typing");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("T-001 should remain a typed source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::DefinitionResult);
    assert_eq!(
        diagnostic.primary.span().range().start(),
        offset(T001.find("value\n\n").expect("equation body"))
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("Bool"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(
        diagnostic.related[0].span().range().start(),
        offset(T001.find("Bool").expect("declared codomain"))
    );
}

#[test]
fn t002_operator_operand_relates_the_bool_to_the_operator() {
    let source = source("t002.ash", T002);
    let error = run_source(source).expect_err("T-002 should fail in typing");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("T-002 should remain a typed source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::OperatorOperand);
    assert_eq!(diagnostic.primary.span().range().start(), 0);
    assert_eq!(diagnostic.primary.span().range().end(), 4);
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(
        diagnostic.related[0].span().range().start(),
        offset(T002.find('+').expect("primitive operator"))
    );
}

#[test]
fn t003_not_applicable_relates_the_function_position_to_the_application() {
    let source = source("t003.ash", T003);
    let error = run_source(source).expect_err("T-003 should fail in typing");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("T-003 should remain a typed source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::NotApplicable);
    assert_eq!(diagnostic.primary.span().range().start(), 0);
    assert_eq!(diagnostic.primary.span().range().end(), 2);
    assert_eq!(diagnostic.expected.as_deref(), Some("function"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span().range().start(), 0);
    assert_eq!(diagnostic.related[0].span().range().end(), 4);
}

#[test]
fn t004_argument_relates_the_argument_to_the_declared_domain() {
    let source = source("t004.ash", T004);
    let error = run_source(source).expect_err("T-004 should fail in typing");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("T-004 should remain a typed source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::Argument);
    assert_eq!(
        diagnostic.primary.span().range().start(),
        offset(T004.rfind("true").expect("argument"))
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
    assert!(diagnostic.related.iter().any(|label| {
        label.span().range().start() == offset(T004.find("Int").expect("declared domain"))
    }));
}

#[test]
fn annotated_binding_initializer_relates_the_expression_to_its_annotation() {
    let source = source("binding-initializer.ash", BINDING_INITIALIZER);
    let tree = parse(lex(&source).expect("binding mismatch should lex"));
    let surface = project(&source, &tree).expect("binding mismatch should project");
    let resolved = resolve(&surface).expect("binding mismatch should resolve");
    let ResolvedExprKind::Block(block) = &resolved.result.kind else {
        panic!("fixture should resolve to a block");
    };
    let binding = binding(block, 0);
    let annotation = binding.annotation.as_ref().expect("binding annotation");
    let error = run_source(source).expect_err("the initializer should not check");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("binding mismatch should be a categorized source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::BindingInitializer);
    assert_eq!(diagnostic.primary.span(), binding.initializer.span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), annotation.span);
    assert_eq!(diagnostic.expected.as_deref(), Some("Bool"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
    assert!(diagnostic.help.is_none());
}

#[test]
fn annotated_binding_keeps_the_whole_nested_initializer_as_primary() {
    let text = "{\n    let value : Bool = {\n        1\n    }\n    value\n}\n";
    let source = source("nested-binding-mismatch.ash", text);
    let tree = parse(lex(&source).expect("nested binding mismatch should lex"));
    let surface = project(&source, &tree).expect("nested binding mismatch should project");
    let resolved = resolve(&surface).expect("nested binding mismatch should resolve");
    let ResolvedExprKind::Block(block) = &resolved.result.kind else {
        panic!("fixture should resolve to a block");
    };
    let binding = binding(block, 0);
    let error = run_source(source).expect_err("the nested initializer should not check");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("nested binding mismatch should be categorized");
    };

    assert_eq!(diagnostic.reason, TypeReason::BindingInitializer);
    assert_eq!(diagnostic.primary.span(), binding.initializer.span);
}

#[test]
fn equational_interface_shape_relates_the_annotation_to_the_equation_head() {
    let source = source("interface.ash", EQUATION_INTERFACE_NOT_FUNCTION);
    let error = run_source(source).expect_err("the interface should require one domain");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("interface shape should remain a typed source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::EquationInterfaceNotFunction);
    assert_eq!(
        diagnostic.primary.span().range().start(),
        offset(
            EQUATION_INTERFACE_NOT_FUNCTION
                .find("Int")
                .expect("interface annotation"),
        )
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("function"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(
        diagnostic.related[0].span().range().start(),
        offset(
            EQUATION_INTERFACE_NOT_FUNCTION
                .find("answer value")
                .expect("equation head"),
        )
    );
}

#[test]
fn anonymous_function_without_an_annotation_relates_to_the_binding_that_requires_synthesis() {
    let source = source("function-context.ash", FUNCTION_NEEDS_CONTEXT);
    let tree = parse(lex(&source).expect("function context should lex"));
    let surface = project(&source, &tree).expect("function context should project");
    let resolved = resolve(&surface).expect("function context should resolve");
    let ResolvedExprKind::Block(block) = &resolved.result.kind else {
        panic!("fixture should resolve to a block");
    };
    let binding_span = binding(block, 0).span;
    let error = run_source(source).expect_err("the anonymous function cannot synthesize");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("missing function context should remain a typed source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(
        diagnostic.primary.span(),
        binding(block, 0).initializer.span
    );
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), binding_span);
    assert_eq!(
        diagnostic.help.as_deref(),
        Some("add a function type annotation to this binding")
    );
}

#[test]
fn anonymous_program_result_records_the_file_position_that_requires_synthesis() {
    let source = source("function-result-context.ash", FUNCTION_RESULT_NEEDS_CONTEXT);
    let tree = parse(lex(&source).expect("function result context should lex"));
    let surface = project(&source, &tree).expect("function result context should project");
    let resolved = resolve(&surface).expect("function result context should resolve");
    let error = run_source(source).expect_err("the program result must synthesize");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("missing program-result context should be a source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), resolved.result.span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), resolved.result.span);
    assert!(diagnostic.help.is_none());
}

#[test]
fn anonymous_function_checked_against_a_non_function_keeps_the_accepted_context_category() {
    let source = source("non-function-context.ash", FUNCTION_NON_FUNCTION_CONTEXT);
    let error = run_source(source).expect_err("an Int is not a function context");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("the provisional non-function context should be a source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert!(diagnostic.expected.is_none());
    assert!(diagnostic.found.is_none());
}

#[test]
fn anonymous_function_in_function_position_relates_to_the_application_that_requires_synthesis() {
    let text = "(fn(value) {\n    value\n}) 1\n";
    let source = source("application-context.ash", text);
    let tree = parse(lex(&source).expect("application context should lex"));
    let surface = project(&source, &tree).expect("application context should project");
    let resolved = resolve(&surface).expect("application context should resolve");
    let ResolvedExprKind::Apply(application) = &resolved.result.kind else {
        panic!("fixture should resolve to an application");
    };
    let error = run_source(source).expect_err("the function position must synthesize");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("missing application context should be a source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), application.function.span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), resolved.result.span);
}

#[test]
fn anonymous_function_operand_relates_to_the_operator_that_requires_synthesis() {
    let text = "(fn(value) {\n    value\n}) + 1\n";
    let source = source("operator-context.ash", text);
    let tree = parse(lex(&source).expect("operator context should lex"));
    let surface = project(&source, &tree).expect("operator context should project");
    let resolved = resolve(&surface).expect("operator context should resolve");
    let ResolvedExprKind::Add(addition) = &resolved.result.kind else {
        panic!("fixture should resolve to addition");
    };
    let error = run_source(source).expect_err("the operand must synthesize");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("missing operator context should be a source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), addition.left.span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), addition.operator_span);
}

#[test]
fn anonymous_function_right_operand_keeps_the_operator_synthesis_context() {
    let text = "1 + (fn(value) {\n    value\n})\n";
    let source = source("right-operator-context.ash", text);
    let tree = parse(lex(&source).expect("right operator context should lex"));
    let surface = project(&source, &tree).expect("right operator context should project");
    let resolved = resolve(&surface).expect("right operator context should resolve");
    let ResolvedExprKind::Add(addition) = &resolved.result.kind else {
        panic!("fixture should resolve to addition");
    };
    let error = run_source(source).expect_err("the right operand must synthesize");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("missing right-operator context should be a source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), addition.right.span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), addition.operator_span);
}

#[test]
fn nested_block_preserves_the_outer_binding_synthesis_context() {
    let text = "{\n    let identity = {\n        fn(value) {\n            value\n        }\n    }\n    identity 1\n}\n";
    let source = source("nested-binding-context.ash", text);
    let tree = parse(lex(&source).expect("nested binding context should lex"));
    let surface = project(&source, &tree).expect("nested binding context should project");
    let resolved = resolve(&surface).expect("nested binding context should resolve");
    let ResolvedExprKind::Block(block) = &resolved.result.kind else {
        panic!("fixture should resolve to a block");
    };
    let outer_binding = binding(block, 0);
    let error = run_source(source).expect_err("the nested function still cannot synthesize");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("nested missing context should be a source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), outer_binding.span);
    assert_eq!(
        diagnostic.help.as_deref(),
        Some("add a function type annotation to this binding")
    );
}
