use ash::{
    lexer::{TokenKind, lex},
    parser::{
        ConcreteElement, Event, ExpectedForm, NodeKind, ParseContext, ParseReason, ProjectionError,
        SynchronizationBoundary, parse, project_module,
    },
    source::SourceFile,
    surface::{SurfaceDeclarationIndex, SurfaceDefinitionKind, SurfaceReference, SurfaceTypeKind},
};

fn spanned_text(source: &SourceFile, span: ash::source::Span) -> &str {
    let range = span.range();
    &source.text()[range.start() as usize..range.end() as usize]
}

fn parse_tree(text: &str) -> (SourceFile, ash::parser::ConcreteTree) {
    let source = SourceFile::new("interface-syntax.ash", text).expect("syntax source should fit");
    let lexed = lex(&source).expect("syntax source should lex");
    assert!(lexed.diagnostics.is_empty(), "{:?}", lexed.diagnostics);
    let tree = parse(lexed);
    assert_complete_balanced_events(&tree);
    (source, tree)
}

fn assert_complete_balanced_events(tree: &ash::parser::ConcreteTree) {
    let mut depth = 0_usize;
    let mut token_indexes = Vec::new();
    for event in tree.events() {
        match event {
            Event::Start(_) => depth = depth.saturating_add(1),
            Event::Token(index) => token_indexes.push(*index),
            Event::Finish => {
                assert!(depth > 0, "a finish event must close an open node");
                depth -= 1;
            }
            Event::Missing { .. } | Event::Error(_) => {}
        }
    }
    assert_eq!(depth, 0, "all concrete nodes must be closed");
    assert_eq!(
        token_indexes,
        (0..tree.tokens().len()).collect::<Vec<_>>(),
        "events must retain the complete lexer token stream exactly once"
    );
}

fn assert_projection_refused(source: &SourceFile, tree: &ash::parser::ConcreteTree) {
    assert_eq!(
        project_module(source, tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn projects_ordered_requirements_on_both_global_presentations() {
    let text = "same : (A, A) -> Bool where Equal<A>, Lib.Show<Option<A>>\nsame pair = true\n\npub fn same_operational(pair : (A, A)) -> Bool where Equal<A>, Lib.Show<Option<A>> {\ntrue\n}\n";
    let source = SourceFile::new("requirements.ash", text).expect("requirement source should fit");
    let tree = parse(lex(&source).expect("requirement source should lex"));
    assert_complete_balanced_events(&tree);

    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).expect("requirements should project");
    let [equational, operational] = module.definitions.as_slice() else {
        panic!("expected both global presentations");
    };

    let SurfaceDefinitionKind::Equational(equational) = &equational.kind else {
        panic!("expected an equational global");
    };
    assert_eq!(equational.interface.requirements.len(), 2);
    assert_eq!(
        spanned_text(&source, equational.interface.annotation.span),
        "(A, A) -> Bool"
    );
    assert_eq!(
        spanned_text(&source, equational.interface.requirements[0].span),
        "Equal<A>"
    );
    assert!(matches!(
        &equational.interface.requirements[0].interface,
        SurfaceReference::Unqualified(name) if name.text == "Equal"
    ));
    assert!(matches!(
        &equational.interface.requirements[1].interface,
        SurfaceReference::Qualified(name)
            if name.qualifier.text == "Lib" && name.member.text == "Show"
    ));
    assert_eq!(
        spanned_text(&source, equational.interface.requirements[1].argument.span),
        "Option<A>"
    );
    assert!(matches!(
        equational.interface.requirements[1].argument.kind,
        SurfaceTypeKind::Application { .. }
    ));

    let SurfaceDefinitionKind::InlineOperational(operational) = &operational.kind else {
        panic!("expected an operational global");
    };
    assert_eq!(operational.header.requirements.len(), 2);
    assert_eq!(
        operational
            .header
            .requirements
            .iter()
            .map(|requirement| spanned_text(&source, requirement.span))
            .collect::<Vec<_>>(),
        vec!["Equal<A>", "Lib.Show<Option<A>>"]
    );
    assert_eq!(
        spanned_text(&source, operational.header.result_type.span),
        "Bool"
    );
}

#[test]
fn projects_generic_impl_prerequisites_and_flat_method_equations() {
    let text = "pub impl Equal<Option<A>> where Equal<A>, Display<A> {\nequal (None, None) = true\nequal (Some(left), Some(right)) = equal (left, right)\n}\n";
    let source = SourceFile::new("generic-impl.ash", text).expect("impl source should fit");
    let tree = parse(lex(&source).expect("impl source should lex"));
    assert_complete_balanced_events(&tree);

    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).expect("impl source should project");
    let [implementation] = module.implementations.as_slice() else {
        panic!("expected one projected implementation");
    };

    assert!(implementation.public);
    assert!(matches!(
        &implementation.interface,
        SurfaceReference::Unqualified(name) if name.text == "Equal"
    ));
    assert_eq!(
        spanned_text(&source, implementation.argument.span),
        "Option<A>"
    );
    assert!(matches!(
        implementation.argument.kind,
        SurfaceTypeKind::Application { .. }
    ));
    assert_eq!(
        implementation
            .prerequisites
            .iter()
            .map(|requirement| spanned_text(&source, requirement.span))
            .collect::<Vec<_>>(),
        vec!["Equal<A>", "Display<A>"]
    );
    assert_eq!(implementation.equations.len(), 2);
    assert!(
        implementation
            .equations
            .iter()
            .all(|equation| equation.name.text == "equal")
    );
    assert_eq!(
        spanned_text(&source, implementation.equations[0].span),
        "equal (None, None) = true"
    );
    assert_eq!(spanned_text(&source, implementation.span), text.trim_end());
}

#[test]
fn accepts_an_empty_impl_body_for_checker_owned_completeness() {
    let text = "impl Equal<Int> {\n}\n";
    let source = SourceFile::new("empty-impl.ash", text).expect("empty impl source should fit");
    let tree = parse(lex(&source).expect("empty impl source should lex"));
    assert_complete_balanced_events(&tree);

    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).expect("empty impl should project");
    let [implementation] = module.implementations.as_slice() else {
        panic!("expected one projected implementation");
    };
    assert!(implementation.equations.is_empty());
    assert_eq!(spanned_text(&source, implementation.span), text.trim_end());
}

#[test]
fn projects_a_qualified_impl_head_without_changing_its_identity_route() {
    let text = "impl Library.Equal<Int> {\n}\n";
    let source = SourceFile::new("qualified-impl.ash", text).expect("qualified impl should fit");
    let tree = parse(lex(&source).expect("qualified impl should lex"));
    assert_complete_balanced_events(&tree);

    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).expect("qualified impl should project");
    assert!(matches!(
        &module.implementations[0].interface,
        SurfaceReference::Qualified(name)
            if name.qualifier.text == "Library"
                && name.member.text == "Equal"
                && spanned_text(&source, name.span) == "Library.Equal"
    ));
}

#[test]
fn projects_mixed_declarations_with_explicit_source_order() {
    let text = "type First = First\ninterface Read<A> {\nread : A -> Int\n}\nvalue : Unit -> Int\nvalue () = 1\nimpl Read<Int> {\nread value = value\n}\npub type Last = Last\npub fn other(value : Int) -> Int {\nvalue\n}\n";
    let source = SourceFile::new("mixed.ash", text).expect("mixed source should fit");
    let tree = parse(lex(&source).expect("mixed source should lex"));
    assert_complete_balanced_events(&tree);

    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).expect("mixed declarations should project");
    assert_eq!(
        module.declaration_order,
        vec![
            SurfaceDeclarationIndex::Type(0),
            SurfaceDeclarationIndex::Interface(0),
            SurfaceDeclarationIndex::Global(0),
            SurfaceDeclarationIndex::Implementation(0),
            SurfaceDeclarationIndex::Type(1),
            SurfaceDeclarationIndex::Global(1),
        ]
    );
    assert_eq!(module.type_declarations.len(), 2);
    assert_eq!(module.interfaces.len(), 1);
    assert_eq!(module.definitions.len(), 2);
    assert_eq!(module.implementations.len(), 1);
}

#[test]
fn malformed_where_clauses_retain_exact_expected_forms() {
    for (case, text) in [
        ("empty where", "same : Unit -> Bool where\nsame () = true\n"),
        (
            "trailing comma",
            "same : Unit -> Bool where Equal<Unit>,\nsame () = true\n",
        ),
    ] {
        let (source, tree) = parse_tree(text);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{case} should retain one diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{case}");
        assert_eq!(
            diagnostic.expected.as_deref(),
            Some("an interface application"),
            "{case}"
        );
        assert_eq!(diagnostic.found.as_deref(), Some("line end"), "{case}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            "\n",
            "{case}"
        );
        assert!(
            matches!(
                diagnostic.context.as_slice(),
                [ParseContext::Synchronization {
                    boundary: SynchronizationBoundary::LogicalLineEnd,
                    span,
                }] if spanned_text(&source, *span) == "\n"
            ),
            "{case}: {:?}",
            diagnostic.context
        );
        assert!(
            matches!(diagnostic.related.as_slice(), [label] if spanned_text(&source, label.span()) == "\n")
        );
        assert_projection_refused(&source, &tree);
    }
}

#[test]
fn malformed_requirement_applications_recover_once_at_the_owner_boundary() {
    for (case, requirement, primary) in [
        ("malformed qualified name", "Lib.<Unit>", "<"),
        ("leading comma", ",", ","),
        ("doubled comma", "Equal<Unit>,,", ","),
    ] {
        let text = format!("same : Unit -> Bool where {requirement}\nsame () = true\n");
        let (source, tree) = parse_tree(&text);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{case} should retain one diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{case}");
        assert_eq!(
            diagnostic.expected.as_deref(),
            Some("an interface application"),
            "{case}"
        );
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            primary,
            "{case}"
        );
        assert!(matches!(
            diagnostic.context.as_slice(),
            [ParseContext::Synchronization {
                boundary: SynchronizationBoundary::LogicalLineEnd,
                span,
            }] if spanned_text(&source, *span) == "\n"
        ));
        assert_projection_refused(&source, &tree);
    }
}

#[test]
fn malformed_interface_and_impl_heads_retain_exact_expected_forms() {
    let cases = [
        (
            "interface parameter",
            "interface Equal {\nequal : Int -> Bool\n}\n",
            "one interface parameter written as <A>",
        ),
        ("impl head", "impl Equal {\n}\n", "an interface application"),
    ];

    for (case, text, expected) in cases {
        let (source, tree) = parse_tree(text);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{case} should retain one diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{case}");
        assert_eq!(diagnostic.expected.as_deref(), Some(expected), "{case}");
        assert_eq!(diagnostic.found.as_deref(), Some("{"), "{case}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            "{",
            "{case}"
        );
        assert_projection_refused(&source, &tree);
    }
}

#[test]
fn a_lowercase_interface_name_recovers_once_at_its_body() {
    let text = "interface equal<A> {\nequal : A -> Bool\n}\n";
    let (source, tree) = parse_tree(text);
    let [diagnostic] = tree.parse_diagnostics() else {
        panic!(
            "the malformed name should retain one diagnostic: {:?}",
            tree.parse_diagnostics()
        );
    };

    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(diagnostic.expected.as_deref(), Some("an identifier"));
    assert_eq!(diagnostic.found.as_deref(), Some("identifier"));
    assert_eq!(spanned_text(&source, diagnostic.primary.span()), "equal");
    assert!(matches!(
        diagnostic.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::InterfaceBodyOpeningBrace,
            span,
        }] if spanned_text(&source, *span) == "{"
    ));
    assert_projection_refused(&source, &tree);
}

#[test]
fn malformed_header_delimiters_recover_once_at_the_owning_boundary() {
    let cases = [
        (
            "extra interface parameter",
            "interface Equal<A, B> {\nequal : A -> Bool\n}\n",
            "one interface parameter written as <A>",
            ",",
            SynchronizationBoundary::InterfaceBodyOpeningBrace,
        ),
        (
            "missing interface parameter",
            "interface Equal<,> {\nequal : A -> Bool\n}\n",
            "one interface parameter written as <A>",
            ",",
            SynchronizationBoundary::InterfaceBodyOpeningBrace,
        ),
        (
            "extra impl argument",
            "impl Equal<Int, Bool> {\n}\n",
            "an interface application",
            ",",
            SynchronizationBoundary::ImplementationBodyOpeningBrace,
        ),
    ];

    for (case, text, expected, primary, boundary) in cases {
        let (source, tree) = parse_tree(text);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{case} should retain one diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{case}");
        assert_eq!(diagnostic.expected.as_deref(), Some(expected), "{case}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            primary,
            "{case}"
        );
        assert!(
            matches!(
                diagnostic.context.as_slice(),
                [ParseContext::Synchronization { boundary: actual, span }]
                    if *actual == boundary && spanned_text(&source, *span) == "{"
            ),
            "{case}: {:?}",
            diagnostic.context
        );
        assert_projection_refused(&source, &tree);
    }
}

#[test]
fn missing_requirement_comma_recovers_once_at_the_header_line() {
    let text = "same : Unit -> Bool where Equal<Unit> Display<Unit>\nsame () = true\n";
    let (source, tree) = parse_tree(text);
    let [diagnostic] = tree.parse_diagnostics() else {
        panic!(
            "missing comma should retain one diagnostic: {:?}",
            tree.parse_diagnostics()
        );
    };

    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(diagnostic.expected.as_deref(), Some(","));
    assert_eq!(diagnostic.found.as_deref(), Some("uppercase identifier"));
    assert_eq!(spanned_text(&source, diagnostic.primary.span()), "Display");
    assert!(matches!(
        diagnostic.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::LogicalLineEnd,
            span,
        }] if spanned_text(&source, *span) == "\n"
    ));
    assert_projection_refused(&source, &tree);
}

#[test]
fn trailing_where_syntax_recovers_once_at_the_owning_header_boundary() {
    let cases = [
        (
            "equational",
            "same : Unit -> Bool where Equal<Unit> -> Bool\nsame () = true\n",
            "a logical line end",
            SynchronizationBoundary::LogicalLineEnd,
            "\n",
        ),
        (
            "operational",
            "fn same(value : Unit) -> Bool where Equal<Unit> -> Bool {\ntrue\n}\n",
            "{",
            SynchronizationBoundary::OperationalBodyOpeningBrace,
            "{",
        ),
        (
            "implementation",
            "impl Equal<Int> where Display<Int> -> Bool {\n}\n",
            "{",
            SynchronizationBoundary::ImplementationBodyOpeningBrace,
            "{",
        ),
    ];

    for (case, text, expected, boundary, synchronized) in cases {
        let (source, tree) = parse_tree(text);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{case} should retain one diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{case}");
        assert_eq!(diagnostic.expected.as_deref(), Some(expected), "{case}");
        assert_eq!(diagnostic.found.as_deref(), Some("->"), "{case}");
        assert_eq!(spanned_text(&source, diagnostic.primary.span()), "->");
        assert!(
            matches!(
                diagnostic.context.as_slice(),
                [ParseContext::Synchronization { boundary: actual, span }]
                    if *actual == boundary && spanned_text(&source, *span) == synchronized
            ),
            "{case}: {:?}",
            diagnostic.context
        );
        assert_projection_refused(&source, &tree);
    }
}

#[test]
fn malformed_interface_method_recovers_at_its_logical_line() {
    let text = "interface Equal<A> {\nequal (A, A) -> Bool\nother : A -> Bool\n}\n";
    let (source, tree) = parse_tree(text);
    let [diagnostic] = tree.parse_diagnostics() else {
        panic!(
            "the malformed method should retain one diagnostic: {:?}",
            tree.parse_diagnostics()
        );
    };

    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(diagnostic.expected.as_deref(), Some(":"));
    assert_eq!(diagnostic.found.as_deref(), Some("("));
    assert_eq!(spanned_text(&source, diagnostic.primary.span()), "(");
    assert!(matches!(
        diagnostic.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::LogicalLineEnd,
            span,
        }] if spanned_text(&source, *span) == "\n"
    ));
    assert!(
        tree.events()
            .iter()
            .any(|event| matches!(event, Event::Start(NodeKind::InterfaceMethod)))
    );
    assert_projection_refused(&source, &tree);
}

#[test]
fn malformed_method_lines_stop_after_the_first_causal_failure() {
    let cases = [
        (
            "missing interface colon",
            "interface Equal<A> {\nequal = true\n}\n",
            ":",
            "=",
        ),
        (
            "non-method interface line",
            "interface Equal<A> {\n42\n}\n",
            "an interface method signature",
            "42",
        ),
        (
            "missing implementation equal",
            "impl Equal<Int> {\nequal value\n}\n",
            "=",
            "\n",
        ),
        (
            "equality operator instead of implementation equal",
            "impl Equal<Int> {\nequal value == true\n}\n",
            "=",
            "==",
        ),
        (
            "missing implementation expression",
            "impl Equal<Int> {\nequal value = = true\n}\n",
            "an expression",
            "=",
        ),
    ];

    for (case, text, expected, primary) in cases {
        let (source, tree) = parse_tree(text);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{case} should retain one diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{case}");
        assert_eq!(diagnostic.expected.as_deref(), Some(expected), "{case}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            primary,
            "{case}"
        );
        assert_projection_refused(&source, &tree);
    }
}

#[test]
fn unexpected_interface_method_start_recovers_to_the_next_logical_line() {
    let text = "interface Equal<A> {\n42\nequal : A -> Bool\n}\n";
    let (source, tree) = parse_tree(text);
    let [diagnostic] = tree.parse_diagnostics() else {
        panic!(
            "the malformed interface line should retain one diagnostic: {:?}",
            tree.parse_diagnostics()
        );
    };

    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(
        diagnostic.expected.as_deref(),
        Some("an interface method signature")
    );
    assert_eq!(diagnostic.found.as_deref(), Some("integer"));
    assert_eq!(spanned_text(&source, diagnostic.primary.span()), "42");
    assert!(matches!(
        diagnostic.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::LogicalLineEnd,
            span,
        }] if spanned_text(&source, *span) == "\n"
    ));
    assert_eq!(
        tree.events()
            .iter()
            .filter(|event| matches!(event, Event::Start(NodeKind::InterfaceMethod)))
            .count(),
        1
    );
    assert_projection_refused(&source, &tree);
}

#[test]
fn recovers_at_an_impl_method_line_and_closing_brace() {
    let cases = [
        (
            "method line",
            "impl Equal<Int> {\nequal = true\nother value = value\n}\n",
            "a pattern",
            "=",
            SynchronizationBoundary::LogicalLineEnd,
            "\n",
        ),
        (
            "impl close",
            "impl Equal<Int> {\nequal value = }\n",
            "an expression",
            "}",
            SynchronizationBoundary::ImplementationClosingBrace,
            "}",
        ),
    ];

    for (case, text, expected, primary, boundary, synchronized) in cases {
        let (source, tree) = parse_tree(text);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{case} should retain one diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{case}");
        assert_eq!(diagnostic.expected.as_deref(), Some(expected), "{case}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            primary,
            "{case}"
        );
        assert!(
            matches!(
                diagnostic.context.as_slice(),
                [ParseContext::Synchronization {
                    boundary: actual,
                    span,
                }] if *actual == boundary && spanned_text(&source, *span) == synchronized
            ),
            "{case}: {:?}",
            diagnostic.context
        );
        assert_projection_refused(&source, &tree);
    }
}

#[test]
fn unexpected_impl_method_start_recovers_to_the_next_logical_line() {
    let text = "impl Equal<Int> {\n42\nequal value = value\n}\n";
    let (source, tree) = parse_tree(text);
    let [diagnostic] = tree.parse_diagnostics() else {
        panic!(
            "the malformed method line should retain one diagnostic: {:?}",
            tree.parse_diagnostics()
        );
    };

    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(
        diagnostic.expected.as_deref(),
        Some("an implementation method equation")
    );
    assert_eq!(diagnostic.found.as_deref(), Some("integer"));
    assert_eq!(spanned_text(&source, diagnostic.primary.span()), "42");
    assert!(matches!(
        diagnostic.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::LogicalLineEnd,
            span,
        }] if spanned_text(&source, *span) == "\n"
    ));
    assert_eq!(
        tree.events()
            .iter()
            .filter(|event| matches!(event, Event::Start(NodeKind::Equation)))
            .count(),
        1
    );
    assert_projection_refused(&source, &tree);
}

#[test]
fn nested_expression_braces_do_not_close_the_owning_impl() {
    let text = "impl Equal<Int> {\nequal value = {\nvalue\n}\nother value = value\n}\n";
    let source = SourceFile::new("nested-impl.ash", text).expect("nested impl should fit");
    let tree = parse(lex(&source).expect("nested impl should lex"));
    assert_complete_balanced_events(&tree);

    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).expect("nested impl should project");
    assert_eq!(module.implementations[0].equations.len(), 2);
}

#[test]
fn misplaced_where_inside_a_value_type_recovers_at_the_header_line() {
    let text = "same : Unit where Equal<Unit> -> Bool\nsame () = true\n";
    let (source, tree) = parse_tree(text);
    let [diagnostic] = tree.parse_diagnostics() else {
        panic!(
            "misplaced where should retain one diagnostic: {:?}",
            tree.parse_diagnostics()
        );
    };

    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(diagnostic.expected.as_deref(), Some("a logical line end"));
    assert_eq!(diagnostic.found.as_deref(), Some("->"));
    assert_eq!(spanned_text(&source, diagnostic.primary.span()), "->");
    assert!(matches!(
        diagnostic.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::LogicalLineEnd,
            span,
        }] if spanned_text(&source, *span) == "\n"
    ));
    assert_projection_refused(&source, &tree);
}

#[test]
fn interface_method_body_is_rejected_at_its_equal_and_recovers() {
    let text = "interface Equal<A> {\nequal : A -> Bool = true\n}\n";
    let (source, tree) = parse_tree(text);
    let [diagnostic] = tree.parse_diagnostics() else {
        panic!(
            "method body should retain one diagnostic: {:?}",
            tree.parse_diagnostics()
        );
    };

    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(diagnostic.expected.as_deref(), Some("a logical line end"));
    assert_eq!(diagnostic.found.as_deref(), Some("="));
    assert_eq!(spanned_text(&source, diagnostic.primary.span()), "=");
    assert!(matches!(
        diagnostic.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::LogicalLineEnd,
            span,
        }] if spanned_text(&source, *span) == "\n"
    ));
    assert_projection_refused(&source, &tree);
}

#[test]
fn impl_where_without_a_head_is_rejected_at_where() {
    let text = "impl where Equal<Int> {\n}\n";
    let (source, tree) = parse_tree(text);
    let [diagnostic] = tree.parse_diagnostics() else {
        panic!(
            "missing impl head should retain one diagnostic: {:?}",
            tree.parse_diagnostics()
        );
    };

    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(
        diagnostic.expected.as_deref(),
        Some("an interface application")
    );
    assert_eq!(diagnostic.found.as_deref(), Some("where"));
    assert_eq!(spanned_text(&source, diagnostic.primary.span()), "where");
    assert!(matches!(
        diagnostic.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::ImplementationBodyOpeningBrace,
            span,
        }] if spanned_text(&source, *span) == "{"
    ));
    assert_projection_refused(&source, &tree);
}

#[test]
fn empty_interface_body_is_parser_owned() {
    let text = "interface Empty<A> {\n}\n";
    let (source, tree) = parse_tree(text);
    let [diagnostic] = tree.parse_diagnostics() else {
        panic!(
            "empty interface should retain one diagnostic: {:?}",
            tree.parse_diagnostics()
        );
    };

    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(
        diagnostic.expected.as_deref(),
        Some("an interface method signature")
    );
    assert_eq!(diagnostic.found.as_deref(), Some("}"));
    assert_eq!(spanned_text(&source, diagnostic.primary.span()), "}");
    assert_projection_refused(&source, &tree);
}

#[test]
fn a_body_brace_on_the_next_line_is_one_rejected_declaration() {
    let cases = [
        (
            "interface",
            "interface Equal<A>\n{\nequal : A -> Bool\n}\n",
            SynchronizationBoundary::InterfaceClosingBrace,
        ),
        (
            "implementation",
            "impl Equal<Int>\n{\nequal value = value\n}\n",
            SynchronizationBoundary::ImplementationClosingBrace,
        ),
        (
            "operational",
            "fn same(value : Int) -> Bool where Equal<Int>\n{\ntrue\n}\n",
            SynchronizationBoundary::BlockClosingBrace,
        ),
    ];

    for (case, text, boundary) in cases {
        let (source, tree) = parse_tree(text);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{case} should retain one diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{case}");
        assert_eq!(diagnostic.expected.as_deref(), Some("{"), "{case}");
        assert_eq!(diagnostic.found.as_deref(), Some("line end"), "{case}");
        assert_eq!(spanned_text(&source, diagnostic.primary.span()), "\n");
        assert!(
            matches!(
                diagnostic.context.as_slice(),
                [ParseContext::Synchronization { boundary: actual, span }]
                    if *actual == boundary && spanned_text(&source, *span) == "}"
            ),
            "{case}: {:?}",
            diagnostic.context
        );
        assert_projection_refused(&source, &tree);
    }
}

#[test]
fn recovery_events_name_the_precise_expected_forms() {
    let (_, tree) = parse_tree("impl Equal<Int> {\nequal value = }\n");
    assert!(tree.events().iter().any(|event| {
        matches!(
            event,
            Event::Missing {
                expected: ExpectedForm::Expression,
                ..
            }
        )
    }));
}

#[test]
fn projects_public_and_private_method_only_interfaces_exactly() {
    let text = "interface Render<A> {\nrender : A -> Int\n}\npub interface Equal<A> {\nequal : (A, A) -> Bool\n}\n";
    let source = SourceFile::new("interfaces.ash", text).expect("interface source should fit");
    let lexed = lex(&source).expect("interface source should lex");

    assert!(lexed.diagnostics.is_empty());
    assert_eq!(
        lexed
            .tokens
            .iter()
            .map(|token| (token.kind.clone(), spanned_text(&source, token.span)))
            .filter(|(kind, _)| {
                matches!(
                    kind,
                    TokenKind::Interface
                        | TokenKind::Pub
                        | TokenKind::UpperIdentifier(_)
                        | TokenKind::Identifier(_)
                )
            })
            .collect::<Vec<_>>(),
        vec![
            (TokenKind::Interface, "interface"),
            (TokenKind::UpperIdentifier("Render".into()), "Render"),
            (TokenKind::UpperIdentifier("A".into()), "A"),
            (TokenKind::Identifier("render".into()), "render"),
            (TokenKind::UpperIdentifier("A".into()), "A"),
            (TokenKind::Pub, "pub"),
            (TokenKind::Interface, "interface"),
            (TokenKind::UpperIdentifier("Equal".into()), "Equal"),
            (TokenKind::UpperIdentifier("A".into()), "A"),
            (TokenKind::Identifier("equal".into()), "equal"),
            (TokenKind::UpperIdentifier("A".into()), "A"),
            (TokenKind::UpperIdentifier("A".into()), "A"),
        ]
    );

    let tree = parse(lexed);
    assert_complete_balanced_events(&tree);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let root = tree.root().expect("the parser should retain a module root");
    assert_eq!(root.kind, NodeKind::Module);
    let interface_nodes = root
        .children
        .iter()
        .filter_map(|child| match child {
            ConcreteElement::Node(node) => Some(node),
            ConcreteElement::Token(_)
            | ConcreteElement::Missing { .. }
            | ConcreteElement::Error(_) => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        interface_nodes
            .iter()
            .map(|node| node.kind)
            .collect::<Vec<_>>(),
        vec![
            NodeKind::InterfaceDeclaration,
            NodeKind::InterfaceDeclaration
        ]
    );
    for node in &interface_nodes {
        assert_eq!(
            node.children
                .iter()
                .filter_map(|child| match child {
                    ConcreteElement::Node(child) => Some(child.kind),
                    ConcreteElement::Token(_)
                    | ConcreteElement::Missing { .. }
                    | ConcreteElement::Error(_) => None,
                })
                .collect::<Vec<_>>(),
            vec![NodeKind::InterfaceMethod]
        );
    }
    let module = project_module(&source, &tree).expect("interface source should project");
    let [private, public] = module.interfaces.as_slice() else {
        panic!("expected two projected interfaces");
    };

    assert!(!private.public);
    assert_eq!(private.name.text, "Render");
    assert_eq!(private.parameter.text, "A");
    assert_eq!(
        spanned_text(&source, private.span),
        text.lines().take(3).collect::<Vec<_>>().join("\n")
    );
    let [method] = private.methods.as_slice() else {
        panic!("expected one private interface method");
    };
    assert_eq!(method.name.text, "render");
    assert_eq!(spanned_text(&source, method.span), "render : A -> Int");
    assert!(matches!(
        method.annotation.kind,
        SurfaceTypeKind::Function(_)
    ));

    assert!(public.public);
    assert_eq!(public.name.text, "Equal");
    assert_eq!(public.parameter.text, "A");
    assert_eq!(
        spanned_text(&source, public.span),
        text.lines().skip(3).take(3).collect::<Vec<_>>().join("\n")
    );
    let [method] = public.methods.as_slice() else {
        panic!("expected one public interface method");
    };
    assert_eq!(method.name.text, "equal");
    assert_eq!(
        spanned_text(&source, method.annotation.span),
        "(A, A) -> Bool"
    );
    assert!(matches!(
        method.annotation.kind,
        SurfaceTypeKind::Function(_)
    ));
}

#[test]
fn preserves_interface_method_source_order() {
    let text = "interface Equal<A> {\nequal : (A, A) -> Bool\nnot_equal : (A, A) -> Bool\n}\n";
    let source = SourceFile::new("method-order.ash", text).expect("method source should fit");
    let tree = parse(lex(&source).expect("method source should lex"));
    assert_complete_balanced_events(&tree);

    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).expect("method source should project");
    assert_eq!(
        module.interfaces[0]
            .methods
            .iter()
            .map(|method| method.name.text.as_str())
            .collect::<Vec<_>>(),
        vec!["equal", "not_equal"]
    );
    assert_eq!(
        module.interfaces[0]
            .methods
            .iter()
            .map(|method| spanned_text(&source, method.span))
            .collect::<Vec<_>>(),
        vec!["equal : (A, A) -> Bool", "not_equal : (A, A) -> Bool"]
    );
}
