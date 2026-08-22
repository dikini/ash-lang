use ash::{
    lexer::{TokenKind, lex},
    parser::{
        Event, NodeKind, ParseContext, ParseReason, ProjectionError, ResourceFailure,
        STRUCTURAL_DEPTH_LIMIT, SynchronizationBoundary, parse, project,
    },
    source::{ByteRange, SourceFile},
    surface::{
        SurfaceBinding, SurfaceBlock, SurfaceDefinitionKind, SurfaceExpr, SurfaceExprKind,
        SurfaceLocalDeclaration, SurfaceTypeKind,
    },
};

fn parse_valid(text: &str) -> (ash::parser::ConcreteTree, ash::surface::SurfaceProgram) {
    let source = SourceFile::new("parser.ash", text).expect("the parser fixture should fit");
    let lexed = lex(&source).expect("lexing should preserve source invariants");
    assert!(lexed.diagnostics.is_empty());
    let tree = parse(lexed);
    let program = project(&source, &tree).expect("the fixture should project");
    (tree, program)
}

fn assert_integer(expression: &SurfaceExpr, expected: &str) {
    let SurfaceExprKind::Integer(value) = &expression.kind else {
        panic!("expected integer expression, found {expression:?}");
    };
    assert_eq!(value.to_string(), expected);
}

fn parse_tree(text: &str) -> (SourceFile, ash::parser::ConcreteTree) {
    let source = SourceFile::new("parser.ash", text).expect("the parser fixture should fit");
    let lexed = lex(&source).expect("lexing should preserve source invariants");
    let tree = parse(lexed);
    (source, tree)
}

fn assert_name(expression: &SurfaceExpr, expected: &str) {
    let SurfaceExprKind::Name(name) = &expression.kind else {
        panic!("expected name expression, found {expression:?}");
    };
    assert_eq!(name.text, expected);
}

fn binding(block: &SurfaceBlock, index: usize) -> &SurfaceBinding {
    let SurfaceLocalDeclaration::Binding(binding) = &block.declarations[index] else {
        panic!("expected ordinary binding")
    };
    binding
}

#[test]
fn projects_recursive_group() {
    let source_text = "{\nlet rec first : Unit -> Int = fn(ignored) {\nsecond ()\n}\nand second : Unit -> Int = fn(ignored) {\n42\n}\nfirst ()\n}\n";
    let (_, program) = parse_valid(source_text);
    let SurfaceExprKind::Block(block) = &program.result.kind else {
        panic!("expected block");
    };
    assert_eq!(block.declarations.len(), 1);
    let SurfaceLocalDeclaration::Recursive(group) = &block.declarations[0] else {
        panic!("expected recursive declaration");
    };
    assert_eq!(group.members.len(), 2);

    let first = &group.members[0];
    assert_eq!(
        &source_text[first.introducer_span.range().start() as usize
            ..first.introducer_span.range().end() as usize],
        "let rec"
    );
    assert_eq!(first.binder.name.text, "first");
    assert_eq!(
        &source_text[first.annotation.span.range().start() as usize
            ..first.annotation.span.range().end() as usize],
        "Unit -> Int"
    );
    assert_eq!(
        &source_text[first.initializer.span.range().start() as usize
            ..first.initializer.span.range().end() as usize],
        "fn(ignored) {\nsecond ()\n}"
    );
    assert_eq!(
        &source_text[first.span.range().start() as usize..first.span.range().end() as usize],
        "first : Unit -> Int = fn(ignored) {\nsecond ()\n}"
    );

    let second = &group.members[1];
    assert_eq!(
        &source_text[second.introducer_span.range().start() as usize
            ..second.introducer_span.range().end() as usize],
        "and"
    );
    assert_eq!(second.binder.name.text, "second");
    assert_eq!(
        &source_text[second.span.range().start() as usize..second.span.range().end() as usize],
        "second : Unit -> Int = fn(ignored) {\n42\n}"
    );
    assert_eq!(
        &source_text[group.span.range().start() as usize..group.span.range().end() as usize],
        "let rec first : Unit -> Int = fn(ignored) {\nsecond ()\n}\nand second : Unit -> Int = fn(ignored) {\n42\n}"
    );
}

#[test]
fn projects_one_member_recursive_group() {
    let (_, program) =
        parse_valid("{\nlet rec answer : Unit -> Int = fn(ignored) {\n42\n}\nanswer ()\n}\n");
    let SurfaceExprKind::Block(block) = &program.result.kind else {
        panic!("expected block");
    };
    let [SurfaceLocalDeclaration::Recursive(group)] = block.declarations.as_slice() else {
        panic!("expected one recursive declaration");
    };
    assert_eq!(group.members.len(), 1);
    assert_eq!(group.members[0].binder.name.text, "answer");
}

#[test]
fn recursive_group_recovery() {
    let cases = [
        (
            "{\nlet rec value = fn(item) {\nitem\n}\nvalue\n}\n",
            ParseReason::ExpectedForm,
        ),
        (
            "{\nlet rec value : Int =\nvalue\n}\n",
            ParseReason::ExpectedForm,
        ),
        (
            "{\nlet rec value : Int = 1\nand\nvalue\n}\n",
            ParseReason::ExpectedRecursiveMember,
        ),
        (
            "{\nand stray : Int = 1\n42\n}\n",
            ParseReason::UnexpectedAnd,
        ),
        (
            "{\nlet rec bad : Int =\nlet later = 1\nlater\n}\n",
            ParseReason::ExpectedForm,
        ),
    ];

    for (text, expected_reason) in cases {
        let (source, tree) = parse_tree(text);
        assert!(
            tree.parse_diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.reason == expected_reason),
            "missing {expected_reason:?} for {text:?}: {:?}",
            tree.parse_diagnostics()
        );
        assert_eq!(
            project(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent)
        );

        let mut depth = 0_u32;
        for event in tree.events() {
            match event {
                Event::Start(_) => depth += 1,
                Event::Finish => {
                    assert!(depth > 0, "unmatched finish for {text:?}");
                    depth -= 1;
                }
                Event::Token(_) | Event::Missing { .. } | Event::Error(_) => {}
            }
        }
        assert_eq!(depth, 0, "unclosed event for {text:?}");
        assert_eq!(
            tree.events()
                .iter()
                .filter_map(|event| match event {
                    Event::Token(index) => Some(*index),
                    _ => None,
                })
                .collect::<Vec<_>>(),
            (0..tree.tokens().len()).collect::<Vec<_>>(),
            "source: {text:?}"
        );
    }

    let (_source, missing_member) = parse_tree("{\nlet rec value : Int = 1\nand\nvalue\n}\n");
    let diagnostic = missing_member
        .parse_diagnostics()
        .iter()
        .find(|diagnostic| diagnostic.reason == ParseReason::ExpectedRecursiveMember)
        .expect("missing member diagnostic");
    assert_eq!(diagnostic.primary.span().range().start(), 29);
    assert_eq!(diagnostic.primary.span().range().end(), 30);
    assert!(matches!(
        diagnostic.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::LogicalLineEnd,
            ..
        }]
    ));
}

#[test]
fn precedence_builds_a_token_complete_tree_and_surface_expression() {
    let (tree, program) = parse_valid("1 + 2 * 3");

    assert_eq!(tree.root().map(|root| root.kind), Some(NodeKind::Program));

    let consumed = tree
        .events()
        .iter()
        .filter_map(|event| match event {
            Event::Token(index) => Some(*index),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(consumed, (0..tree.tokens().len()).collect::<Vec<_>>());

    let SurfaceExprKind::Add(add) = &program.result.kind else {
        panic!("expected addition, found {:?}", program.result);
    };
    assert_integer(&add.left, "1");
    let SurfaceExprKind::Multiply(multiply) = &add.right.kind else {
        panic!("expected multiplication, found {:?}", add.right);
    };
    assert_integer(&multiply.left, "2");
    assert_integer(&multiply.right, "3");
}

#[test]
fn application_multiplication_and_addition_associate_to_the_left() {
    let (_, application) = parse_valid("f a b");
    let SurfaceExprKind::Apply(outer) = &application.result.kind else {
        panic!("expected outer application");
    };
    assert_name(&outer.argument, "b");
    let SurfaceExprKind::Apply(inner) = &outer.function.kind else {
        panic!("expected left-associated inner application");
    };
    assert_name(&inner.function, "f");
    assert_name(&inner.argument, "a");

    let (_, multiplication) = parse_valid("1 * 2 * 3");
    let SurfaceExprKind::Multiply(outer) = &multiplication.result.kind else {
        panic!("expected outer multiplication");
    };
    assert_integer(&outer.right, "3");
    assert!(matches!(outer.left.kind, SurfaceExprKind::Multiply(_)));

    let (_, addition) = parse_valid("1 + 2 + 3");
    let SurfaceExprKind::Add(outer) = &addition.result.kind else {
        panic!("expected outer addition");
    };
    assert_integer(&outer.right, "3");
    assert!(matches!(outer.left.kind, SurfaceExprKind::Add(_)));
}

#[test]
fn equality_is_non_associative() {
    let (source, tree) = parse_tree("1 == 2 == 3");

    assert_eq!(
        tree.parse_diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.reason)
            .collect::<Vec<_>>(),
        vec![ParseReason::RepeatedEquality]
    );
    assert_eq!(
        project(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn grouping_erases_to_the_inner_surface_kind_but_retains_the_group_span() {
    let (_, program) = parse_valid("(1 + 2)");

    assert!(matches!(program.result.kind, SurfaceExprKind::Add(_)));
    assert_eq!(program.result.span.range().start(), 0);
    assert_eq!(program.result.span.range().end(), 7);
}

#[test]
fn grouped_name_retains_the_identifier_token_span_inside_the_group_span() {
    let (_, program) = parse_valid("(unknown)");

    assert_eq!(program.result.span.range().start(), 0);
    assert_eq!(program.result.span.range().end(), 9);
    let SurfaceExprKind::Name(name) = &program.result.kind else {
        panic!("expected a grouped name");
    };
    assert_eq!(name.text, "unknown");
    assert_eq!(name.span.range().start(), 1);
    assert_eq!(name.span.range().end(), 8);
}

#[test]
fn primitive_expression_forms_project_without_semantic_group_nodes() {
    let (_, boolean) = parse_valid("true");
    assert_eq!(boolean.result.kind, SurfaceExprKind::Boolean(true));

    let (_, unit) = parse_valid("()");
    assert_eq!(unit.result.kind, SurfaceExprKind::Unit);

    let (_, name) = parse_valid("value");
    assert_name(&name.result, "value");
}

#[test]
fn function_arrows_associate_to_the_right_and_grouped_types_retain_spans() {
    let (_, program) =
        parse_valid("apply : (Int -> Int) -> Int\napply operation = operation 1\n\napply");
    let SurfaceDefinitionKind::Equational(definition) = &program.definitions[0].kind else {
        panic!("expected equational definition");
    };
    let SurfaceTypeKind::Function(outer) = &definition.interface.annotation.kind else {
        panic!("expected outer function type");
    };
    assert_eq!(outer.domain.span.range().start(), 8);
    assert_eq!(outer.domain.span.range().end(), 20);
    assert!(matches!(outer.domain.kind, SurfaceTypeKind::Function(_)));
    assert_eq!(outer.codomain.kind, SurfaceTypeKind::Int);

    let (_, right_associated) = parse_valid("f : Int -> Bool -> Unit\nf value = value\n\nf");
    let SurfaceDefinitionKind::Equational(definition) = &right_associated.definitions[0].kind
    else {
        panic!("expected equational definition");
    };
    let SurfaceTypeKind::Function(outer) = &definition.interface.annotation.kind else {
        panic!("expected outer function type");
    };
    assert_eq!(outer.domain.kind, SurfaceTypeKind::Int);
    assert!(matches!(outer.codomain.kind, SurfaceTypeKind::Function(_)));
}

#[test]
fn both_v002_presentations_preserve_their_distinct_source_structure() {
    let (_, equational) =
        parse_valid("increment : Int -> Int\nincrement value = value + 1\n\nincrement 41\n");
    let SurfaceDefinitionKind::Equational(equational_definition) = &equational.definitions[0].kind
    else {
        panic!("expected equational definition");
    };
    assert_eq!(equational_definition.interface.span.range().start(), 0);
    assert_eq!(equational_definition.interface.span.range().end(), 22);
    assert_eq!(equational_definition.interface.name.text, "increment");
    assert_eq!(equational_definition.interface.name.span.range().start(), 0);
    assert_eq!(equational_definition.interface.name.span.range().end(), 9);
    assert_eq!(
        equational_definition
            .interface
            .annotation
            .span
            .range()
            .start(),
        12
    );
    assert_eq!(
        equational_definition
            .interface
            .annotation
            .span
            .range()
            .end(),
        22
    );
    assert_eq!(equational_definition.equation.span.range().start(), 23);
    assert_eq!(equational_definition.equation.span.range().end(), 50);
    assert_eq!(equational_definition.equation.name.text, "increment");
    assert_eq!(equational_definition.equation.name.span.range().start(), 23);
    assert_eq!(equational_definition.equation.name.span.range().end(), 32);
    assert_eq!(
        equational_definition.equation.binder.span.range().start(),
        33
    );
    assert_eq!(equational_definition.equation.binder.span.range().end(), 38);
    assert_eq!(equational_definition.equation.body.span.range().start(), 41);
    assert_eq!(equational_definition.equation.body.span.range().end(), 50);
    let SurfaceExprKind::Add(equational_add) = &equational_definition.equation.body.kind else {
        panic!("expected equational addition body");
    };
    assert_eq!(equational_add.operator_span.range().start(), 47);
    assert_eq!(equational_add.operator_span.range().end(), 48);

    let (_, operational) =
        parse_valid("fn increment(value : Int) -> Int {\n    value + 1\n}\n\nincrement 41\n");
    let SurfaceDefinitionKind::InlineOperational(operational_definition) =
        &operational.definitions[0].kind
    else {
        panic!("expected inline operational definition");
    };
    assert_eq!(operational_definition.header.span.range().start(), 0);
    assert_eq!(operational_definition.header.span.range().end(), 32);
    assert_eq!(operational_definition.header.name.text, "increment");
    assert_eq!(operational_definition.header.name.span.range().start(), 3);
    assert_eq!(operational_definition.header.name.span.range().end(), 12);
    assert_eq!(
        operational_definition.header.parameter.span.range().start(),
        13
    );
    assert_eq!(
        operational_definition.header.parameter.span.range().end(),
        24
    );
    assert_eq!(
        operational_definition
            .header
            .result_type
            .span
            .range()
            .start(),
        29
    );
    assert_eq!(
        operational_definition.header.result_type.span.range().end(),
        32
    );
    assert_eq!(operational_definition.body.span.range().start(), 33);
    assert_eq!(operational_definition.body.span.range().end(), 50);
    assert_eq!(operational_definition.body.result.span.range().start(), 39);
    assert_eq!(operational_definition.body.result.span.range().end(), 48);
    let SurfaceExprKind::Add(operational_add) = &operational_definition.body.result.kind else {
        panic!("expected operational addition body");
    };
    assert_eq!(operational_add.operator_span.range().start(), 45);
    assert_eq!(operational_add.operator_span.range().end(), 46);
}

#[test]
fn blocks_bindings_annotations_and_anonymous_functions_project() {
    let (_, shadowing) =
        parse_valid("{\n    let value = 1\n    let value = value + 1\n    value\n}\n");
    let SurfaceExprKind::Block(block) = &shadowing.result.kind else {
        panic!("expected block");
    };
    assert_eq!(block.declarations.len(), 2);
    assert!(block.declarations.iter().all(|declaration| matches!(
        declaration,
        SurfaceLocalDeclaration::Binding(binding) if binding.annotation.is_none()
    )));

    let (_, capture) = parse_valid(
        "{\n    let offset = 40\n    let add_offset : Int -> Int = fn(value) {\n        value + offset\n    }\n    add_offset 2\n}\n",
    );
    let SurfaceExprKind::Block(block) = &capture.result.kind else {
        panic!("expected capture block");
    };
    let SurfaceLocalDeclaration::Binding(binding) = &block.declarations[1] else {
        panic!("expected ordinary binding")
    };
    assert!(binding.annotation.is_some());
    assert!(matches!(
        binding.initializer.kind,
        SurfaceExprKind::Function(_)
    ));
}

#[test]
fn mixed_globals_and_nested_application_project_in_program_order() {
    let (_, program) = parse_valid(
        "increment : Int -> Int\nincrement value = value + 1\n\nfn double(value : Int) -> Int {\n    value * 2\n}\n\ndouble (increment 20)\n",
    );

    assert_eq!(program.definitions.len(), 2);
    assert!(matches!(
        program.definitions[0].kind,
        SurfaceDefinitionKind::Equational(_)
    ));
    assert!(matches!(
        program.definitions[1].kind,
        SurfaceDefinitionKind::InlineOperational(_)
    ));
    let SurfaceExprKind::Apply(outer) = &program.result.kind else {
        panic!("expected outer application");
    };
    assert_name(&outer.function, "double");
    assert!(matches!(outer.argument.kind, SurfaceExprKind::Apply(_)));
}

#[test]
fn higher_order_operational_parameter_and_parenthesized_function_argument_project() {
    let (_, program) = parse_valid(
        "fn apply(operation : Int -> Int) -> Int {\n    operation 41\n}\n\napply (fn(value) {\n    value + 1\n})\n",
    );

    let SurfaceDefinitionKind::InlineOperational(definition) = &program.definitions[0].kind else {
        panic!("expected inline operational definition");
    };
    assert!(matches!(
        definition.header.parameter.annotation.kind,
        SurfaceTypeKind::Function(_)
    ));
    let SurfaceExprKind::Apply(application) = &program.result.kind else {
        panic!("expected application");
    };
    assert!(matches!(
        application.argument.kind,
        SurfaceExprKind::Function(_)
    ));
}

#[test]
fn excluded_structural_forms_report_owned_reasons_and_never_project() {
    let cases = [
        ("(1, 2)", ParseReason::TupleSyntax),
        ("match value {\n    true\n}", ParseReason::MatchSyntax),
        (
            "fn add(left : Int, right : Int) -> Int {\n    left\n}\n\nadd\n",
            ParseReason::MultipleParameters,
        ),
        (
            "add : Int -> Int\nadd left right = left\n\nadd\n",
            ParseReason::MultipleBinders,
        ),
        (
            "fn identity<a>(value : Int) -> Int {\n    value\n}\n\nidentity\n",
            ParseReason::PolymorphicHeader,
        ),
        ("1;", ParseReason::Semicolon),
    ];

    for (text, expected_reason) in cases {
        let (source, tree) = parse_tree(text);
        assert!(
            tree.parse_diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.reason == expected_reason),
            "missing {expected_reason:?} for {text:?}: {:?}",
            tree.parse_diagnostics()
        );
        assert_eq!(
            project(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "source: {text:?}"
        );
        let consumed = tree
            .events()
            .iter()
            .filter_map(|event| match event {
                Event::Token(index) => Some(*index),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            consumed,
            (0..tree.tokens().len()).collect::<Vec<_>>(),
            "source: {text:?}"
        );
    }
}

#[test]
fn missing_final_result_and_lexical_errors_are_hard_projection_boundaries() {
    let (source, tree) = parse_tree("increment : Int -> Int\nincrement value = value + 1\n");
    assert!(
        tree.parse_diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.reason == ParseReason::ExpectedResult)
    );
    assert_eq!(
        project(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );

    let (source, lexical_tree) = parse_tree("1 /* excluded */");
    assert!(!lexical_tree.lexical_diagnostics().is_empty());
    assert_eq!(
        project(&source, &lexical_tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn recovery_events_remain_balanced_and_retain_mismatched_delimiters() {
    for text in ["(", "{\n1\n)", "fn(value, other) {\nvalue\n}"] {
        let (_source, tree) = parse_tree(text);
        let mut depth = 0_u32;
        for event in tree.events() {
            match event {
                Event::Start(_) => depth += 1,
                Event::Finish => {
                    assert!(depth > 0, "unmatched finish for {text:?}");
                    depth -= 1;
                }
                Event::Token(_) | Event::Missing { .. } | Event::Error(_) => {}
            }
        }
        assert_eq!(depth, 0, "unclosed event for {text:?}");
        assert_eq!(
            tree.events()
                .iter()
                .filter_map(|event| match event {
                    Event::Token(index) => Some(*index),
                    _ => None,
                })
                .collect::<Vec<_>>(),
            (0..tree.tokens().len()).collect::<Vec<_>>(),
            "source: {text:?}"
        );
        assert!(
            tree.events()
                .iter()
                .any(|event| matches!(event, Event::Error(_))),
            "source: {text:?}"
        );
    }
}

#[test]
fn every_surface_construct_retains_its_complete_accepted_span() {
    let (_, program) = parse_valid(
        "fn increment(value : Int) -> Int {\n    let one : Int = 1\n    value + one\n}\n\nincrement 41\n",
    );
    let definition = &program.definitions[0];
    assert_eq!(definition.span.range().start(), 0);
    assert_eq!(definition.span.range().end(), 74);
    let SurfaceDefinitionKind::InlineOperational(definition) = &definition.kind else {
        panic!("expected inline definition");
    };
    assert_eq!(definition.header.name.span.range().start(), 3);
    assert_eq!(definition.header.parameter.span.range().start(), 13);
    assert_eq!(definition.header.parameter.span.range().end(), 24);
    assert_eq!(binding(&definition.body, 0).span.range().start(), 39);
    assert_eq!(binding(&definition.body, 0).span.range().end(), 56);
    assert_eq!(program.span.range().start(), 0);
    assert_eq!(program.span.range().end(), 89);
}

#[test]
fn accepted_parser_cases_have_focused_reasons_and_primary_spans() {
    let (_source, missing_result) =
        parse_tree("fn increment(value : Int) -> Int {\n    value + 1\n}\n");
    let diagnostic = &missing_result.parse_diagnostics()[0];
    assert_eq!(diagnostic.reason, ParseReason::ExpectedResult);
    assert_eq!(diagnostic.primary.span().range().start(), 51);
    assert_eq!(diagnostic.primary.span().range().end(), 51);
    let [
        ParseContext::PrecedingGlobalComplete {
            starting_at,
            ending_at,
            line_end,
        },
    ] = diagnostic.context.as_slice()
    else {
        panic!("expected one completed-global context: {diagnostic:?}");
    };
    assert_eq!(starting_at.range().start(), 0);
    assert_eq!(starting_at.range().end(), 2);
    assert_eq!(ending_at.range().start(), 49);
    assert_eq!(ending_at.range().end(), 50);
    assert_eq!(line_end.range().start(), 50);
    assert_eq!(line_end.range().end(), 51);

    let (_source, unclosed) =
        parse_tree("increment : Int -> Int\nincrement value = value + 1\n\nincrement (41");
    let diagnostic = unclosed
        .parse_diagnostics()
        .iter()
        .find(|diagnostic| diagnostic.reason == ParseReason::UnclosedGroup)
        .expect("the unclosed group should be diagnosed");
    assert_eq!(diagnostic.primary.span().range().start(), 62);
    assert_eq!(diagnostic.primary.span().range().end(), 63);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span().range().start(), 65);
    assert_eq!(diagnostic.related[0].span().range().end(), 65);
    assert_eq!(diagnostic.expected.as_deref(), Some(")"));
    assert_eq!(diagnostic.found.as_deref(), Some("end of input"));

    let (_source, two_failures) =
        parse_tree("fn increment(value : Int) -> Int {\n    value +\n}\n\nincrement (41");
    assert_eq!(
        two_failures
            .parse_diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.reason)
            .collect::<Vec<_>>(),
        vec![ParseReason::ExpectedOperand, ParseReason::UnclosedGroup]
    );
    assert_eq!(
        two_failures.parse_diagnostics()[0]
            .primary
            .span()
            .range()
            .start(),
        45
    );
    assert_eq!(
        two_failures.parse_diagnostics()[0].expected.as_deref(),
        Some("an operand")
    );
    assert_eq!(
        two_failures.parse_diagnostics()[0].found.as_deref(),
        Some("line end")
    );
    assert_eq!(two_failures.parse_diagnostics()[0].related.len(), 1);
    assert_eq!(
        two_failures.parse_diagnostics()[0].related[0]
            .span()
            .range()
            .start(),
        47
    );
    assert_eq!(
        two_failures.parse_diagnostics()[0].related[0]
            .span()
            .range()
            .end(),
        48
    );
    let [ParseContext::Synchronization { boundary, span }] =
        two_failures.parse_diagnostics()[0].context.as_slice()
    else {
        panic!("expected one synchronization context");
    };
    assert_eq!(*boundary, SynchronizationBoundary::BlockClosingBrace);
    assert_eq!(span.range().start(), 47);
    assert_eq!(span.range().end(), 48);
    assert_eq!(
        two_failures.parse_diagnostics()[1]
            .primary
            .span()
            .range()
            .start(),
        60
    );
}

#[test]
fn logical_line_ends_stop_unparenthesized_infix_but_not_grouped_syntax() {
    let (_, grouped) = parse_valid("(1 +\n 2)");
    assert!(matches!(grouped.result.kind, SurfaceExprKind::Add(_)));

    let (source, split) = parse_tree("1 +\n2");
    assert!(
        split
            .parse_diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.reason == ParseReason::ExpectedOperand)
    );
    assert_eq!(
        project(&source, &split),
        Err(ProjectionError::RecoveryNodesPresent)
    );

    let (_, grouped_type) = parse_valid("f : (Int ->\n Bool) -> Unit\nf value = ()\n\nf");
    let SurfaceDefinitionKind::Equational(definition) = &grouped_type.definitions[0].kind else {
        panic!("expected equational definition");
    };
    let SurfaceTypeKind::Function(function) = &definition.interface.annotation.kind else {
        panic!("expected outer function type");
    };
    assert!(matches!(function.domain.kind, SurfaceTypeKind::Function(_)));
}

#[test]
fn canonical_polymorphic_punctuation_remains_a_lexical_projection_boundary() {
    let (source, tree) =
        parse_tree("fn identity<A>(value : Int) -> Int {\n    value\n}\n\nidentity\n");

    assert!(!tree.lexical_diagnostics().is_empty());
    assert_eq!(
        project(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn projection_rejects_a_tree_against_a_different_source_identity() {
    let source = SourceFile::new("first.ash", "1").expect("the first source should fit");
    let lexed = lex(&source).expect("lexing should preserve source invariants");
    let tree = parse(lexed);
    let other = SourceFile::new("second.ash", "1").expect("the second source should fit");

    assert_eq!(
        project(&other, &tree),
        Err(ProjectionError::MalformedTree(
            ash::parser::InternalReason::ForeignSpan
        ))
    );
}

#[test]
fn projection_rejects_a_foreign_interior_operator_span() {
    let source = SourceFile::new("parser.ash", "1 + 2").expect("the source should fit");
    let foreign = SourceFile::new("foreign.ash", "1 + 2").expect("the foreign source should fit");
    let mut lexed = lex(&source).expect("the source should lex");
    let operator = lexed
        .tokens
        .iter_mut()
        .find(|token| token.kind == TokenKind::Plus)
        .expect("the fixture has one plus token");
    operator.span = foreign
        .span(ByteRange::new(2, 3).expect("the range is ordered"))
        .expect("the foreign operator range is valid");
    let tree = parse(lexed);

    assert_eq!(
        project(&source, &tree),
        Err(ProjectionError::MalformedTree(
            ash::parser::InternalReason::ForeignSpan
        ))
    );
}

#[test]
fn projection_rejects_out_of_order_retained_token_spans() {
    let source = SourceFile::new("parser.ash", "1 + 2").expect("the source should fit");
    let mut lexed = lex(&source).expect("the source should lex");
    let first = lexed.tokens[0].span;
    lexed.tokens[0].span = lexed.tokens[2].span;
    lexed.tokens[2].span = first;
    let tree = parse(lexed);

    assert_eq!(
        project(&source, &tree),
        Err(ProjectionError::MalformedTree(
            ash::parser::InternalReason::TokenOutOfOrder
        ))
    );
}

#[test]
fn projection_rejects_an_eof_token_away_from_the_source_end() {
    let source = SourceFile::new("parser.ash", "1").expect("the source should fit");
    let mut lexed = lex(&source).expect("the source should lex");
    let eof = lexed.tokens.last_mut().expect("the lexer retains EOF");
    eof.span = source
        .span(ByteRange::new(0, 0).expect("the range is ordered"))
        .expect("the nonterminal point belongs to the source");
    let tree = parse(lexed);

    assert_eq!(
        project(&source, &tree),
        Err(ProjectionError::MalformedTree(
            ash::parser::InternalReason::InvalidSpan
        ))
    );
}

#[test]
fn v007_retains_single_equality_and_primitive_operator_spans() {
    let (_, program) = parse_valid("(20 + 1) == 21");

    let SurfaceExprKind::Equal(equality) = &program.result.kind else {
        panic!("expected equality");
    };
    assert_eq!(equality.operator_span.range().start(), 9);
    assert_eq!(equality.operator_span.range().end(), 11);
    let SurfaceExprKind::Add(addition) = &equality.left.kind else {
        panic!("expected grouped addition on the left");
    };
    assert_eq!(addition.operator_span.range().start(), 4);
    assert_eq!(addition.operator_span.range().end(), 5);
    assert_integer(&equality.right, "21");
}

#[test]
fn crlf_programs_retain_two_byte_boundaries_and_surface_spans() {
    let text = "increment : Int -> Int\r\nincrement value = value + 1\r\n\r\nincrement 41\r\n";
    let (tree, program) = parse_valid(text);
    let line_ends = tree
        .tokens()
        .iter()
        .filter(|token| matches!(token.kind, ash::lexer::TokenKind::LineEnd))
        .map(|token| (token.span.range().start(), token.span.range().end()))
        .collect::<Vec<_>>();
    assert_eq!(line_ends, vec![(22, 24), (51, 53), (67, 69)]);

    let SurfaceDefinitionKind::Equational(definition) = &program.definitions[0].kind else {
        panic!("expected equational definition");
    };
    assert_eq!(definition.interface.span.range().start(), 0);
    assert_eq!(definition.interface.span.range().end(), 22);
    assert_eq!(definition.equation.span.range().start(), 24);
    assert_eq!(definition.equation.span.range().end(), 51);
    let SurfaceExprKind::Add(addition) = &definition.equation.body.kind else {
        panic!("expected addition body");
    };
    assert_eq!(addition.operator_span.range().start(), 48);
    assert_eq!(addition.operator_span.range().end(), 49);
    assert_eq!(program.result.span.range().start(), 55);
    assert_eq!(program.result.span.range().end(), 67);
    assert_eq!(program.span.range().end(), 69);
}

#[test]
fn local_binding_missing_operand_synchronizes_at_its_line_end() {
    let (_source, tree) = parse_tree("{\n    let value = 1 +\n    value\n}\n");
    let diagnostics = tree
        .parse_diagnostics()
        .iter()
        .filter(|diagnostic| diagnostic.reason == ParseReason::ExpectedOperand)
        .collect::<Vec<_>>();
    assert_eq!(diagnostics.len(), 1);
    let diagnostic = diagnostics[0];

    assert_eq!(diagnostic.primary.span().range().start(), 20);
    assert_eq!(diagnostic.primary.span().range().end(), 21);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span().range().start(), 21);
    assert_eq!(diagnostic.related[0].span().range().end(), 22);
    let [ParseContext::Synchronization { boundary, span }] = diagnostic.context.as_slice() else {
        panic!("the initializer diagnostic needs one synchronization context");
    };
    assert_eq!(*boundary, SynchronizationBoundary::LogicalLineEnd);
    assert_eq!(span.range().start(), 21);
    assert_eq!(span.range().end(), 22);
    assert_ne!(span.range().start(), 32);
}

#[test]
fn nested_local_binding_missing_operand_does_not_leak_to_an_outer_brace() {
    let (_source, tree) = parse_tree(
        "{\n    let outer = {\n        let inner = 1 +\n        inner\n    }\n    outer\n}\n",
    );
    let diagnostics = tree
        .parse_diagnostics()
        .iter()
        .filter(|diagnostic| diagnostic.reason == ParseReason::ExpectedOperand)
        .collect::<Vec<_>>();
    assert_eq!(diagnostics.len(), 1);
    let diagnostic = diagnostics[0];

    assert_eq!(diagnostic.primary.span().range().start(), 42);
    assert_eq!(diagnostic.primary.span().range().end(), 43);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span().range().start(), 43);
    assert_eq!(diagnostic.related[0].span().range().end(), 44);
    let [ParseContext::Synchronization { boundary, span }] = diagnostic.context.as_slice() else {
        panic!("the nested initializer needs one synchronization context");
    };
    assert_eq!(*boundary, SynchronizationBoundary::LogicalLineEnd);
    assert_eq!(span.range().start(), 43);
    assert_eq!(span.range().end(), 44);
    assert_ne!(span.range().start(), 62);
    assert_ne!(span.range().start(), 74);
}

fn assert_depth_boundary(make_source: fn(usize) -> String) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, move || {
                let accepted_source =
                    SourceFile::new("depth-boundary.ash", make_source(STRUCTURAL_DEPTH_LIMIT))
                        .expect("the boundary source should fit");
                let accepted =
                    parse(lex(&accepted_source).expect("the boundary source should lex"));
                assert_eq!(accepted.resource_failure(), None);
                project(&accepted_source, &accepted).expect("the boundary should project");

                let rejected_source = SourceFile::new(
                    "depth-overflow.ash",
                    make_source(STRUCTURAL_DEPTH_LIMIT + 1),
                )
                .expect("the overflow source should fit");
                let rejected =
                    parse(lex(&rejected_source).expect("the overflow source should lex"));
                assert_eq!(
                    rejected.resource_failure(),
                    Some(ResourceFailure::StructuralDepth {
                        limit: STRUCTURAL_DEPTH_LIMIT
                    })
                );
                assert_eq!(
                    project(&rejected_source, &rejected),
                    Err(ProjectionError::ResourceLimit(
                        ResourceFailure::StructuralDepth {
                            limit: STRUCTURAL_DEPTH_LIMIT
                        }
                    ))
                );
                assert!(rejected.lexical_diagnostics().is_empty());
                assert!(rejected.parse_diagnostics().is_empty());
                assert!(
                    !rejected
                        .events()
                        .iter()
                        .any(|event| matches!(event, Event::Error(_) | Event::Missing { .. }))
                );
                let retained = rejected
                    .events()
                    .iter()
                    .filter_map(|event| match event {
                        Event::Token(index) => Some(*index),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                assert_eq!(retained, (0..rejected.tokens().len()).collect::<Vec<_>>());
                let mut event_depth = 0_usize;
                for event in rejected.events() {
                    match event {
                        Event::Start(_) => event_depth += 1,
                        Event::Finish => {
                            assert!(event_depth > 0, "resource recovery emitted an extra finish");
                            event_depth -= 1;
                        }
                        Event::Token(_) | Event::Missing { .. } | Event::Error(_) => {}
                    }
                }
                assert_eq!(event_depth, 0, "resource recovery left an unclosed event");
            })
            .expect("the small-stack depth test should start")
            .join()
            .expect("the small-stack depth test should not abort");
    });
}

#[test]
fn structural_depth_budget_bounds_nested_groups() {
    assert_depth_boundary(|depth| format!("{}1{}", "(".repeat(depth), ")".repeat(depth)));
}

#[test]
fn structural_depth_parser_stage_fits_the_small_stack_at_the_budget() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, || {
                let text = format!(
                    "{}1{}",
                    "(".repeat(STRUCTURAL_DEPTH_LIMIT),
                    ")".repeat(STRUCTURAL_DEPTH_LIMIT)
                );
                let source =
                    SourceFile::new("parse-depth.ash", text).expect("the source should fit");
                let tree = parse(lex(&source).expect("the source should lex"));
                assert_eq!(tree.resource_failure(), None);
                assert_eq!(
                    tree.events()
                        .iter()
                        .filter(|event| matches!(event, Event::Token(_)))
                        .count(),
                    tree.tokens().len()
                );
            })
            .expect("the parser-stage thread should start")
            .join()
            .expect("the parser stage should fit the small stack");
    });
}

#[test]
fn structural_depth_budget_bounds_right_associated_arrows() {
    assert_depth_boundary(|depth| {
        format!("f : {}Int\nf value = value\n\nf", "Int -> ".repeat(depth))
    });
}

#[test]
fn structural_depth_budget_bounds_parenthesized_types() {
    assert_depth_boundary(|depth| {
        format!(
            "f : {}Int{}\nf value = value\n\nf",
            "(".repeat(depth),
            ")".repeat(depth)
        )
    });
}

#[test]
fn structural_depth_budget_bounds_nested_blocks() {
    assert_depth_boundary(|depth| format!("{}1\n{}", "{\n".repeat(depth), "}\n".repeat(depth)));
}

#[test]
fn structural_depth_budget_bounds_mixed_functions_and_blocks() {
    assert_depth_boundary(|depth| {
        let mut expression = "1".to_owned();
        for _ in 0..(depth / 2) {
            expression = format!("fn(value) {{\n{expression}\n}}");
        }
        if depth % 2 == 1 {
            expression = format!("{{\n{expression}\n}}");
        }
        expression
    });
}

#[test]
fn structural_depth_budget_bounds_left_associated_additions() {
    assert_depth_boundary(|depth| format!("1{}", " + 1".repeat(depth)));
}

#[test]
fn structural_depth_budget_bounds_left_associated_applications() {
    assert_depth_boundary(|depth| format!("f{}", " value".repeat(depth)));
}

#[test]
fn far_over_budget_operator_input_has_linear_bounded_construction() {
    let text = format!("1{}", " + 1".repeat(10_000));
    let source = SourceFile::new("scaling.ash", text).expect("the scaling source should fit");
    let tree = parse(lex(&source).expect("the scaling source should lex"));

    assert_eq!(
        tree.resource_failure(),
        Some(ResourceFailure::StructuralDepth {
            limit: STRUCTURAL_DEPTH_LIMIT
        })
    );
    let retained = tree
        .events()
        .iter()
        .filter(|event| matches!(event, Event::Token(_)))
        .count();
    assert_eq!(retained, tree.tokens().len());
    assert!(
        tree.events().len() <= tree.tokens().len() + 4 * STRUCTURAL_DEPTH_LIMIT + 16,
        "event construction must remain token-linear after the bounded prefix"
    );
}
