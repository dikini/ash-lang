use ash::{
    lexer::{TokenKind, lex},
    parser::{
        Event, NodeKind, ParseContext, ParseReason, ProjectionError, ResourceFailure,
        STRUCTURAL_DEPTH_LIMIT, SYNTAX_WORK_LIMIT, SynchronizationBoundary, parse,
        project_module as project,
    },
    source::{ByteRange, SourceFile},
    surface::{
        SurfaceBinding, SurfaceBlock, SurfaceDefinitionKind, SurfaceExpr, SurfaceExprKind,
        SurfaceLocalDeclaration, SurfaceReference, SurfaceTypeKind,
    },
};

struct ProjectedModuleFixture {
    type_declarations: Vec<ash::surface::SurfaceTypeDeclaration>,
    definitions: Vec<ash::surface::SurfaceDefinition>,
    main_body: SurfaceExpr,
    span: ash::source::Span,
}

fn parse_valid(text: &str) -> (ash::parser::ConcreteTree, ProjectedModuleFixture) {
    let text = module_fixture(text);
    let source = SourceFile::new("parser.ash", text).expect("the parser fixture should fit");
    let lexed = lex(&source).expect("lexing should preserve source invariants");
    assert!(lexed.diagnostics.is_empty());
    let tree = parse(lexed);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "unexpected parse diagnostics: {:?}",
        tree.parse_diagnostics()
    );
    let mut module = project(&source, &tree).expect("the fixture should project");
    let main = module
        .definitions
        .pop()
        .expect("the fixture adapter adds a local main definition");
    let SurfaceDefinitionKind::Equational(main) = main.kind else {
        panic!("the fixture adapter adds an equational main definition");
    };
    let result = main
        .equations
        .into_iter()
        .next()
        .expect("the fixture adapter adds one main equation")
        .body;
    (
        tree,
        ProjectedModuleFixture {
            type_declarations: module.type_declarations,
            definitions: module.definitions,
            main_body: result,
            span: module.span,
        },
    )
}

fn module_fixture(text: &str) -> String {
    if text.contains("\nmain : ") || text.starts_with("main : ") {
        let mut module = text.to_owned();
        if !module.ends_with('\n') {
            module.push('\n');
        }
        return module;
    }
    let text = text.strip_suffix('\n').unwrap_or(text);
    let split = text
        .rsplit_once("\n\n")
        .or_else(|| text.rsplit_once("\r\n\r\n"));
    let mut module = if let Some((declarations, result)) = split {
        format!("{declarations}\n\nmain : Unit\nmain () = {result}")
    } else {
        format!("main : Unit\nmain () = {text}")
    };
    module.push('\n');
    module
}

fn expression_fixture_slice<'a>(text: &'a str, span: &ash::source::Span) -> &'a str {
    const PREFIX_LEN: usize = "main : Unit\nmain () = ".len();
    let start = span.range().start() as usize - PREFIX_LEN;
    let end = span.range().end() as usize - PREFIX_LEN;
    &text[start..end]
}

fn assert_integer(expression: &SurfaceExpr, expected: &str) {
    let SurfaceExprKind::Integer(value) = &expression.kind else {
        panic!("expected integer expression, found {expression:?}");
    };
    assert_eq!(value.to_string(), expected);
}

fn parse_tree(text: &str) -> (SourceFile, ash::parser::ConcreteTree) {
    let source =
        SourceFile::new("parser.ash", module_fixture(text)).expect("the parser fixture should fit");
    let lexed = lex(&source).expect("lexing should preserve source invariants");
    let tree = parse(lexed);
    (source, tree)
}

fn assert_name(expression: &SurfaceExpr, expected: &str) {
    let SurfaceExprKind::Name(SurfaceReference::Unqualified(name)) = &expression.kind else {
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

fn concrete_kinds(tree: &ash::parser::ConcreteTree) -> Vec<NodeKind> {
    let mut kinds = Vec::new();
    let mut pending = tree.root().into_iter().collect::<Vec<_>>();
    while let Some(node) = pending.pop() {
        kinds.push(node.kind);
        pending.extend(node.children.iter().filter_map(|child| match child {
            ash::parser::ConcreteElement::Node(child) => Some(child),
            ash::parser::ConcreteElement::Token(_)
            | ash::parser::ConcreteElement::Missing { .. }
            | ash::parser::ConcreteElement::Error(_) => None,
        }));
    }
    kinds
}

fn retained_reason_code(reason: ParseReason) -> &'static str {
    match reason {
        ParseReason::ExpectedForm => "parse.expected-form",
        ParseReason::ExpectedOperand => "parse.expected-operand",
        ParseReason::UnclosedGroup => "parse.unclosed-group",
        ParseReason::RepeatedEquality => "parse.repeated-equality",
        ParseReason::PolymorphicHeader => "parse.polymorphic-header",
        ParseReason::ExpectedRecursiveMember => "parse.expected-recursive-member",
        ParseReason::UnexpectedAnd => "parse.unexpected-and",
        ParseReason::Semicolon => "parse.semicolon",
        ParseReason::UnexpectedToken => "parse.unexpected-token",
    }
}

#[test]
fn public_parse_reasons_describe_only_retained_diagnostics() {
    for reason in [
        ParseReason::ExpectedForm,
        ParseReason::ExpectedOperand,
        ParseReason::UnclosedGroup,
        ParseReason::RepeatedEquality,
        ParseReason::PolymorphicHeader,
        ParseReason::ExpectedRecursiveMember,
        ParseReason::UnexpectedAnd,
        ParseReason::Semicolon,
        ParseReason::UnexpectedToken,
    ] {
        assert_eq!(retained_reason_code(reason), reason.to_string());
    }
}

#[test]
fn data_and_pattern_forms_build_one_token_complete_concrete_tree() {
    let source = "type Tree =\n    Tip(Int)\n    | Fork(Tree, Tree)\n\ntype Choice =\n    Choice((Bool, Tree))\n\nsize : Tree -> Int\nsize (Tip value) = 1\nsize (Fork(left, right)) = size left + size right\n\nfn choose(flag : Bool, tree : Tree) -> Int {\n    match (flag, tree) {\n        (true, Tip(value)) => value\n        (_, Fork(left, right)) => size left + size right\n        (_, Tip(value)) => value\n    }\n}\n\nchoose(true, Tip(42))\n";
    let (_source, tree) = parse_tree(source);

    assert!(tree.lexical_diagnostics().is_empty());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let kinds = concrete_kinds(&tree);
    for expected in [
        NodeKind::TypeDeclaration,
        NodeKind::ConstructorDeclaration,
        NodeKind::Pattern,
        NodeKind::TuplePattern,
        NodeKind::MatchExpression,
        NodeKind::MatchArm,
        NodeKind::TupleExpression,
        NodeKind::TupleType,
    ] {
        assert!(kinds.contains(&expected), "missing {expected:?}: {kinds:?}");
    }
    assert_eq!(
        tree.events()
            .iter()
            .filter_map(|event| match event {
                Event::Token(index) => Some(*index),
                _ => None,
            })
            .collect::<Vec<_>>(),
        (0..tree.tokens().len()).collect::<Vec<_>>()
    );
}

#[test]
fn data_and_pattern_recovery_stays_balanced_and_synchronizes_at_the_arm_line() {
    let text = "match true {\n    true 1\n    false => 2\n}\n";
    let (source, tree) = parse_tree(text);

    let diagnostic = tree
        .parse_diagnostics()
        .iter()
        .find(|diagnostic| {
            diagnostic.reason == ParseReason::ExpectedForm
                && diagnostic.expected.as_deref() == Some("=>")
        })
        .expect("the missing arm arrow should have one structured diagnostic");
    assert!(matches!(
        diagnostic.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::LogicalLineEnd,
            ..
        }]
    ));
    assert_eq!(
        project(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
    assert_eq!(
        tree.events()
            .iter()
            .filter_map(|event| match event {
                Event::Token(index) => Some(*index),
                _ => None,
            })
            .collect::<Vec<_>>(),
        (0..tree.tokens().len()).collect::<Vec<_>>()
    );
    let mut depth = 0_u32;
    for event in tree.events() {
        match event {
            Event::Start(_) => depth += 1,
            Event::Finish => depth -= 1,
            Event::Token(_) | Event::Missing { .. } | Event::Error(_) => {}
        }
    }
    assert_eq!(depth, 0);
}

#[test]
fn projects_data_declarations_tuples_matches_and_pattern_vectors() {
    let source = "type Tree =\n    Tip(Int)\n    | Fork(Tree, Tree)\n\nsize : Tree -> Int\nsize (Tip value) = 1\nsize (Fork(left, right)) = size left + size right\n\nmatch (true, Tip(42)) {\n    (true, Tip(value)) => value\n    (_, Fork(left, right)) => size left + size right\n    (_, Tip(value)) => value\n}\n";
    let (_tree, program) = parse_valid(source);

    assert_eq!(program.type_declarations.len(), 1);
    assert_eq!(program.type_declarations[0].name.text, "Tree");
    assert_eq!(program.type_declarations[0].constructors.len(), 2);
    assert_eq!(program.type_declarations[0].constructors[1].fields.len(), 2);
    let SurfaceDefinitionKind::Equational(definition) = &program.definitions[0].kind else {
        panic!("expected equational definition");
    };
    assert_eq!(definition.equations.len(), 2);
    assert_eq!(definition.equations[0].patterns.len(), 1);
    assert!(matches!(
        definition.equations[0].patterns[0].kind,
        ash::surface::SurfacePatternKind::Constructor { .. }
    ));
    let SurfaceExprKind::Match(match_expression) = &program.main_body.kind else {
        panic!("expected structured match");
    };
    assert!(matches!(
        match_expression.scrutinee.kind,
        SurfaceExprKind::Tuple(_)
    ));
    assert_eq!(match_expression.arms.len(), 3);
}

#[test]
fn projects_recursive_group() {
    let source_text = "{\nlet rec first : Unit -> Int = fn(ignored) {\nsecond ()\n}\nand second : Unit -> Int = fn(ignored) {\n42\n}\nfirst ()\n}\n";
    let (_, program) = parse_valid(source_text);
    let SurfaceExprKind::Block(block) = &program.main_body.kind else {
        panic!("expected block");
    };
    assert_eq!(block.declarations.len(), 1);
    let SurfaceLocalDeclaration::Recursive(group) = &block.declarations[0] else {
        panic!("expected recursive declaration");
    };
    assert_eq!(group.members.len(), 2);

    let first = &group.members[0];
    assert_eq!(
        expression_fixture_slice(source_text, &first.introducer_span),
        "let rec"
    );
    assert_eq!(first.binder.name.text, "first");
    assert_eq!(
        expression_fixture_slice(source_text, &first.annotation.span),
        "Unit -> Int"
    );
    assert_eq!(
        expression_fixture_slice(source_text, &first.initializer.span),
        "fn(ignored) {\nsecond ()\n}"
    );
    assert_eq!(
        expression_fixture_slice(source_text, &first.span),
        "first : Unit -> Int = fn(ignored) {\nsecond ()\n}"
    );

    let second = &group.members[1];
    assert_eq!(
        expression_fixture_slice(source_text, &second.introducer_span),
        "and"
    );
    assert_eq!(second.binder.name.text, "second");
    assert_eq!(
        expression_fixture_slice(source_text, &second.span),
        "second : Unit -> Int = fn(ignored) {\n42\n}"
    );
    assert_eq!(
        expression_fixture_slice(source_text, &group.span),
        "let rec first : Unit -> Int = fn(ignored) {\nsecond ()\n}\nand second : Unit -> Int = fn(ignored) {\n42\n}"
    );
}

#[test]
fn projects_one_member_recursive_group() {
    let (_, program) =
        parse_valid("{\nlet rec answer : Unit -> Int = fn(ignored) {\n42\n}\nanswer ()\n}\n");
    let SurfaceExprKind::Block(block) = &program.main_body.kind else {
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
    assert_eq!(diagnostic.primary.span().range().start(), 51);
    assert_eq!(diagnostic.primary.span().range().end(), 52);
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

    assert_eq!(tree.root().map(|root| root.kind), Some(NodeKind::Module));

    let consumed = tree
        .events()
        .iter()
        .filter_map(|event| match event {
            Event::Token(index) => Some(*index),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(consumed, (0..tree.tokens().len()).collect::<Vec<_>>());

    let SurfaceExprKind::Add(add) = &program.main_body.kind else {
        panic!("expected addition, found {:?}", program.main_body);
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
    let SurfaceExprKind::Apply(outer) = &application.main_body.kind else {
        panic!("expected outer application");
    };
    assert_name(&outer.argument, "b");
    let SurfaceExprKind::Apply(inner) = &outer.function.kind else {
        panic!("expected left-associated inner application");
    };
    assert_name(&inner.function, "f");
    assert_name(&inner.argument, "a");

    let (_, multiplication) = parse_valid("1 * 2 * 3");
    let SurfaceExprKind::Multiply(outer) = &multiplication.main_body.kind else {
        panic!("expected outer multiplication");
    };
    assert_integer(&outer.right, "3");
    assert!(matches!(outer.left.kind, SurfaceExprKind::Multiply(_)));

    let (_, addition) = parse_valid("1 + 2 + 3");
    let SurfaceExprKind::Add(outer) = &addition.main_body.kind else {
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

    assert!(matches!(program.main_body.kind, SurfaceExprKind::Add(_)));
    assert_eq!(program.main_body.span.range().start(), 22);
    assert_eq!(program.main_body.span.range().end(), 29);
}

#[test]
fn grouped_name_retains_the_identifier_token_span_inside_the_group_span() {
    let (_, program) = parse_valid("(unknown)");

    assert_eq!(program.main_body.span.range().start(), 22);
    assert_eq!(program.main_body.span.range().end(), 31);
    let SurfaceExprKind::Name(SurfaceReference::Unqualified(name)) = &program.main_body.kind else {
        panic!("expected a grouped name");
    };
    assert_eq!(name.text, "unknown");
    assert_eq!(name.span.range().start(), 23);
    assert_eq!(name.span.range().end(), 30);
}

#[test]
fn primitive_expression_forms_project_without_semantic_group_nodes() {
    let (_, boolean) = parse_valid("true");
    assert_eq!(boolean.main_body.kind, SurfaceExprKind::Boolean(true));

    let (_, unit) = parse_valid("()");
    assert_eq!(unit.main_body.kind, SurfaceExprKind::Unit);

    let (_, name) = parse_valid("value");
    assert_name(&name.main_body, "value");
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
    let equation = &equational_definition.equations[0];
    assert_eq!(equation.span.range().start(), 23);
    assert_eq!(equation.span.range().end(), 50);
    assert_eq!(equation.name.text, "increment");
    assert_eq!(equation.name.span.range().start(), 23);
    assert_eq!(equation.name.span.range().end(), 32);
    let ash::surface::SurfacePatternKind::Binder(equation_binder) = &equation.patterns[0].kind
    else {
        panic!("expected equation binder");
    };
    assert_eq!(equation_binder.span.range().start(), 33);
    assert_eq!(equation_binder.span.range().end(), 38);
    assert_eq!(equation.body.span.range().start(), 41);
    assert_eq!(equation.body.span.range().end(), 50);
    let SurfaceExprKind::Add(equational_add) = &equation.body.kind else {
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
        operational_definition.header.parameters[0]
            .span
            .range()
            .start(),
        13
    );
    assert_eq!(
        operational_definition.header.parameters[0]
            .span
            .range()
            .end(),
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
    let SurfaceExprKind::Block(block) = &shadowing.main_body.kind else {
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
    let SurfaceExprKind::Block(block) = &capture.main_body.kind else {
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
    let SurfaceExprKind::Apply(outer) = &program.main_body.kind else {
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
        definition.header.parameters[0].annotation.kind,
        SurfaceTypeKind::Function(_)
    ));
    let SurfaceExprKind::Apply(application) = &program.main_body.kind else {
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
fn declarations_only_modules_project_and_lexical_errors_remain_a_hard_boundary() {
    let source = SourceFile::new(
        "declarations.ash",
        "increment : Int -> Int\nincrement value = value + 1\n",
    )
    .expect("the declaration module should fit");
    let tree = parse(lex(&source).expect("the declaration module should lex"));
    assert!(tree.parse_diagnostics().is_empty());
    project(&source, &tree).expect("a declarations-only module should project");

    let (source, lexical_tree) = parse_tree("1 /* excluded */");
    assert!(!lexical_tree.lexical_diagnostics().is_empty());
    assert_eq!(
        project(&source, &lexical_tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn recovery_events_remain_balanced_and_retain_mismatched_delimiters() {
    for text in ["(", "{\n1\n)", "fn(value,, other) {\nvalue\n}"] {
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
    assert_eq!(definition.header.parameters[0].span.range().start(), 13);
    assert_eq!(definition.header.parameters[0].span.range().end(), 24);
    assert_eq!(binding(&definition.body, 0).span.range().start(), 39);
    assert_eq!(binding(&definition.body, 0).span.range().end(), 56);
    assert_eq!(program.span.range().start(), 0);
    assert_eq!(program.span.range().end(), 111);
}

#[test]
fn accepted_parser_cases_have_focused_reasons_and_primary_spans() {
    let (_source, unclosed) =
        parse_tree("increment : Int -> Int\nincrement value = value + 1\n\nincrement (41");
    let diagnostic = unclosed
        .parse_diagnostics()
        .iter()
        .find(|diagnostic| diagnostic.reason == ParseReason::UnclosedGroup)
        .expect("the unclosed group should be diagnosed");
    assert_eq!(diagnostic.primary.span().range().start(), 84);
    assert_eq!(diagnostic.primary.span().range().end(), 85);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span().range().start(), 88);
    assert_eq!(diagnostic.related[0].span().range().end(), 88);
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
        82
    );
}

#[test]
fn logical_line_ends_stop_unparenthesized_infix_but_not_grouped_syntax() {
    let (_, grouped) = parse_valid("(1 +\n 2)");
    assert!(matches!(grouped.main_body.kind, SurfaceExprKind::Add(_)));

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
fn value_level_polymorphic_headers_remain_a_parser_projection_boundary() {
    let (source, tree) =
        parse_tree("fn identity<A>(value : Int) -> Int {\n    value\n}\n\nidentity\n");

    assert!(tree.lexical_diagnostics().is_empty());
    assert!(
        tree.parse_diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.reason == ParseReason::PolymorphicHeader)
    );
    assert_eq!(
        project(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn parameterized_declarations_and_type_applications_project() {
    let (_, program) = parse_valid(
        "type Option<A> =\nNone\n| Some(A)\n\nid : Option<Int> -> Option<Int>\nid value = value\n\nid None\n",
    );

    assert_eq!(program.type_declarations[0].parameters[0].text, "A");
    let SurfaceDefinitionKind::Equational(definition) = &program.definitions[0].kind else {
        panic!("expected equational definition");
    };
    let SurfaceTypeKind::Function(function) = &definition.interface.annotation.kind else {
        panic!("expected function annotation");
    };
    let SurfaceTypeKind::Application {
        constructor,
        arguments,
    } = &function.domain.kind
    else {
        panic!("expected applied nominal domain");
    };
    assert_eq!(constructor.member().text, "Option");
    assert!(matches!(arguments[0].kind, SurfaceTypeKind::Int));
}

#[test]
fn primitive_types_reject_type_arguments_before_projection() {
    for primitive in ["Int", "Bool", "Unit"] {
        let text = format!("bad : {primitive}<Int> -> Int\nbad value = 0\n\n0\n");
        let (source, tree) = parse_tree(&text);

        assert_eq!(
            tree.parse_diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.reason)
                .collect::<Vec<_>>(),
            vec![ParseReason::UnexpectedToken]
        );
        assert_eq!(
            project(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent)
        );
    }
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

    let SurfaceExprKind::Equal(equality) = &program.main_body.kind else {
        panic!("expected equality");
    };
    assert_eq!(equality.operator_span.range().start(), 31);
    assert_eq!(equality.operator_span.range().end(), 33);
    let SurfaceExprKind::Add(addition) = &equality.left.kind else {
        panic!("expected grouped addition on the left");
    };
    assert_eq!(addition.operator_span.range().start(), 26);
    assert_eq!(addition.operator_span.range().end(), 27);
    assert_integer(&equality.right, "21");
}

#[test]
fn crlf_modules_retain_two_byte_boundaries_and_surface_spans() {
    let text = "increment : Int -> Int\r\nincrement value = value + 1\r\n\r\nmain : Unit\r\nmain () = increment 41\r\n";
    let (tree, program) = parse_valid(text);
    let line_ends = tree
        .tokens()
        .iter()
        .filter(|token| matches!(token.kind, ash::lexer::TokenKind::LineEnd))
        .map(|token| (token.span.range().start(), token.span.range().end()))
        .collect::<Vec<_>>();
    assert_eq!(line_ends, vec![(22, 24), (51, 53), (66, 68), (90, 92)]);

    let SurfaceDefinitionKind::Equational(definition) = &program.definitions[0].kind else {
        panic!("expected equational definition");
    };
    assert_eq!(definition.interface.span.range().start(), 0);
    assert_eq!(definition.interface.span.range().end(), 22);
    assert_eq!(definition.equations[0].span.range().start(), 24);
    assert_eq!(definition.equations[0].span.range().end(), 51);
    let SurfaceExprKind::Add(addition) = &definition.equations[0].body.kind else {
        panic!("expected addition body");
    };
    assert_eq!(addition.operator_span.range().start(), 48);
    assert_eq!(addition.operator_span.range().end(), 49);
    assert_eq!(program.main_body.span.range().start(), 78);
    assert_eq!(program.main_body.span.range().end(), 90);
    assert_eq!(program.span.range().end(), 92);
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

    assert_eq!(diagnostic.primary.span().range().start(), 42);
    assert_eq!(diagnostic.primary.span().range().end(), 43);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span().range().start(), 43);
    assert_eq!(diagnostic.related[0].span().range().end(), 44);
    let [ParseContext::Synchronization { boundary, span }] = diagnostic.context.as_slice() else {
        panic!("the initializer diagnostic needs one synchronization context");
    };
    assert_eq!(*boundary, SynchronizationBoundary::LogicalLineEnd);
    assert_eq!(span.range().start(), 43);
    assert_eq!(span.range().end(), 44);
    assert_ne!(span.range().start(), 54);
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

    assert_eq!(diagnostic.primary.span().range().start(), 64);
    assert_eq!(diagnostic.primary.span().range().end(), 65);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span().range().start(), 65);
    assert_eq!(diagnostic.related[0].span().range().end(), 66);
    let [ParseContext::Synchronization { boundary, span }] = diagnostic.context.as_slice() else {
        panic!("the nested initializer needs one synchronization context");
    };
    assert_eq!(*boundary, SynchronizationBoundary::LogicalLineEnd);
    assert_eq!(span.range().start(), 65);
    assert_eq!(span.range().end(), 66);
    assert_ne!(span.range().start(), 84);
    assert_ne!(span.range().start(), 96);
}

fn assert_depth_boundary(make_source: fn(usize) -> String) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, move || {
                let accepted_source = SourceFile::new(
                    "depth-boundary.ash",
                    module_fixture(&make_source(STRUCTURAL_DEPTH_LIMIT)),
                )
                .expect("the boundary source should fit");
                let accepted =
                    parse(lex(&accepted_source).expect("the boundary source should lex"));
                assert_eq!(accepted.resource_failure(), None);
                project(&accepted_source, &accepted).expect("the boundary should project");

                let rejected_source = SourceFile::new(
                    "depth-overflow.ash",
                    module_fixture(&make_source(STRUCTURAL_DEPTH_LIMIT + 1)),
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
                let source = SourceFile::new("parse-depth.ash", module_fixture(&text))
                    .expect("the source should fit");
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

fn nested_constructor_pattern_source(depth: usize) -> String {
    let mut source = "type Loop =\nEnd\n| Step(Loop)\n\nmatch End {\n".to_owned();
    source.push_str(&"Step(".repeat(depth));
    source.push('_');
    source.push_str(&")".repeat(depth));
    source.push_str(" => 1\n_ => 0\n}\n");
    source
}

#[test]
fn structural_depth_budget_bounds_nested_constructor_patterns() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, || {
                let accepted_depth = STRUCTURAL_DEPTH_LIMIT / 8 - 4;
                let accepted_source = SourceFile::new(
                    "pattern-depth-boundary.ash",
                    module_fixture(&nested_constructor_pattern_source(accepted_depth)),
                )
                .expect("the boundary source should fit");
                let accepted = parse(lex(&accepted_source).expect("the boundary should lex"));
                assert_eq!(accepted.resource_failure(), None);
                project(&accepted_source, &accepted).expect("the boundary should project");

                let rejected_source = SourceFile::new(
                    "pattern-depth-overflow.ash",
                    module_fixture(&nested_constructor_pattern_source(accepted_depth + 1)),
                )
                .expect("the overflow source should fit");
                let rejected = parse(lex(&rejected_source).expect("the overflow should lex"));
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

                let far_source = SourceFile::new(
                    "pattern-depth-far-overflow.ash",
                    module_fixture(&nested_constructor_pattern_source(1_000)),
                )
                .expect("the far-overflow source should fit");
                let far = parse(lex(&far_source).expect("the far overflow should lex"));
                assert_eq!(
                    far.resource_failure(),
                    Some(ResourceFailure::StructuralDepth {
                        limit: STRUCTURAL_DEPTH_LIMIT
                    })
                );
            })
            .expect("the pattern-depth thread should start")
            .join()
            .expect("pattern depth should fit the small stack");
    });
}

fn nested_match_source(depth: usize) -> String {
    let mut source = "match true {\n_ => ".repeat(depth);
    source.push('0');
    source.push('\n');
    source.push_str(&"}\n".repeat(depth));
    source
}

#[test]
fn structural_depth_budget_bounds_nested_matches() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, || {
                let accepted_depth = STRUCTURAL_DEPTH_LIMIT / 32;
                let accepted_source = SourceFile::new(
                    "match-depth-boundary.ash",
                    module_fixture(&nested_match_source(accepted_depth)),
                )
                .expect("the boundary source should fit");
                let accepted = parse(lex(&accepted_source).expect("the boundary should lex"));
                assert_eq!(accepted.resource_failure(), None);
                project(&accepted_source, &accepted).expect("the boundary should project");

                let rejected_source = SourceFile::new(
                    "match-depth-overflow.ash",
                    module_fixture(&nested_match_source(accepted_depth + 1)),
                )
                .expect("the overflow source should fit");
                let rejected = parse(lex(&rejected_source).expect("the overflow should lex"));
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

                let far_source = SourceFile::new(
                    "match-depth-far-overflow.ash",
                    module_fixture(&nested_match_source(1_000)),
                )
                .expect("the far-overflow source should fit");
                let far = parse(lex(&far_source).expect("the far overflow should lex"));
                assert_eq!(
                    far.resource_failure(),
                    Some(ResourceFailure::StructuralDepth {
                        limit: STRUCTURAL_DEPTH_LIMIT
                    })
                );
            })
            .expect("the match-depth thread should start")
            .join()
            .expect("match depth should fit the small stack");
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
    let source = SourceFile::new("scaling.ash", module_fixture(&text))
        .expect("the scaling source should fit");
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
        tree.events().len() <= tree.tokens().len() + 4 * STRUCTURAL_DEPTH_LIMIT + 64,
        "event construction must remain token-linear after the bounded prefix"
    );
}

#[test]
fn cumulative_syntax_work_stops_before_constructing_an_oversized_tree() {
    const WIDTH: usize = 110_000;
    let mut text = String::with_capacity(WIDTH * 5 + 32);
    text.push_str("match (");
    for index in 0..WIDTH {
        if index > 0 {
            text.push_str(", ");
        }
        text.push('0');
    }
    text.push_str(") {\n(");
    for index in 0..WIDTH {
        if index > 0 {
            text.push_str(", ");
        }
        text.push('_');
    }
    text.push_str(") => 0\n}\n");
    let source = SourceFile::new("syntax-work-limit.ash", module_fixture(&text))
        .expect("the syntax work fixture should fit");

    let tree = parse(lex(&source).expect("the syntax work fixture should lex"));

    assert_eq!(
        tree.resource_failure(),
        Some(ResourceFailure::SyntaxWork {
            limit: SYNTAX_WORK_LIMIT
        })
    );
    assert!(tree.root().is_none());
    assert!(tree.events().is_empty());
    assert!(tree.lexical_diagnostics().is_empty());
    assert!(tree.parse_diagnostics().is_empty());
    assert_eq!(
        project(&source, &tree),
        Err(ProjectionError::ResourceLimit(
            ResourceFailure::SyntaxWork {
                limit: SYNTAX_WORK_LIMIT
            }
        ))
    );
}
