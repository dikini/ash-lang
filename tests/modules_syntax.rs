use ash::{
    integer::Integer,
    lexer::{TokenKind, lex},
    parser::{
        ConcreteElement, Event, ExpectedForm, NodeKind, ParseReason, ProjectionError, parse,
        project_module,
    },
    source::SourceFile,
    surface::{
        SurfaceDefinitionKind, SurfaceExprKind, SurfaceImportSelection, SurfaceModulePath,
        SurfacePatternKind, SurfaceReference, SurfaceTypeKind, SurfaceTypeVisibility,
    },
};

type ExpectedParserDiagnostic<'a> = (ParseReason, Option<&'a str>, Option<&'a str>, u32, u32);

fn parse_valid(text: &str) -> ash::surface::SurfaceModule {
    let source = SourceFile::new("module.ash", text).expect("module source should fit");
    let lexed = lex(&source).expect("module source should lex");
    assert!(lexed.diagnostics.is_empty(), "{:?}", lexed.diagnostics);
    let tree = parse(lexed);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert_eq!(tree.root().map(|root| root.kind), Some(NodeKind::Module));
    project_module(&source, &tree).expect("module source should project")
}

fn spanned_text(source: &SourceFile, span: ash::source::Span) -> &str {
    let range = span.range();
    &source.text()[range.start() as usize..range.end() as usize]
}

fn assert_parser_rejected(case: &str, text: &str) {
    let source = SourceFile::new("rejected-module.ash", text).expect("module source should fit");
    let lexed = lex(&source).expect("module source should lex");
    assert!(
        lexed.diagnostics.is_empty(),
        "{case} should reach the parser: {:?}",
        lexed.diagnostics
    );
    let tree = parse(lexed);
    assert!(
        !tree.parse_diagnostics().is_empty(),
        "{case} was accepted without a parser diagnostic"
    );
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent),
        "{case} should stop at the parser recovery boundary"
    );
}

fn assert_exact_parser_diagnostics(
    case: &str,
    tree: &ash::parser::ConcreteTree,
    expected: &[ExpectedParserDiagnostic<'_>],
) {
    assert_eq!(tree.parse_diagnostics().len(), expected.len(), "{case}");
    for (diagnostic, &(reason, expected_form, found, start, end)) in
        tree.parse_diagnostics().iter().zip(expected)
    {
        assert_eq!(diagnostic.reason, reason, "{case}");
        assert_eq!(diagnostic.expected.as_deref(), expected_form, "{case}");
        assert_eq!(diagnostic.found.as_deref(), found, "{case}");
        assert_eq!(diagnostic.primary.span().range().start(), start, "{case}");
        assert_eq!(diagnostic.primary.span().range().end(), end, "{case}");
        assert!(diagnostic.related.is_empty(), "{case}");
        assert!(diagnostic.context.is_empty(), "{case}");
    }
}

#[test]
fn modular_reserved_words_and_path_punctuation_are_closed_tokens() {
    let source = SourceFile::new(
        "tokens.ash",
        "import @std.collections.list as List\npub opaque type T = T(Int)\ninterface impl where\n",
    )
    .expect("token source should fit");
    let lexed = lex(&source).expect("token source should lex");

    assert!(lexed.diagnostics.is_empty());
    assert!(
        lexed
            .tokens
            .iter()
            .any(|token| token.kind == TokenKind::Import)
    );
    assert!(lexed.tokens.iter().any(|token| token.kind == TokenKind::At));
    assert!(
        lexed
            .tokens
            .iter()
            .any(|token| token.kind == TokenKind::Dot)
    );
    assert!(lexed.tokens.iter().any(|token| token.kind == TokenKind::As));
    assert!(
        lexed
            .tokens
            .iter()
            .any(|token| token.kind == TokenKind::Pub)
    );
    assert!(
        lexed
            .tokens
            .iter()
            .any(|token| token.kind == TokenKind::Opaque)
    );
    assert!(
        lexed
            .tokens
            .iter()
            .any(|token| token.kind == TokenKind::Interface)
    );
    assert!(
        lexed
            .tokens
            .iter()
            .any(|token| token.kind == TokenKind::Impl)
    );
    assert!(
        lexed
            .tokens
            .iter()
            .any(|token| token.kind == TokenKind::Where)
    );
}

#[test]
fn public_inline_operational_global_is_exact_through_projection() {
    let text = "pub fn increment(value : Int) -> Int {\n    value + 1\n}\n";
    let source = SourceFile::new("public-operational.ash", text).expect("source should fit");
    let lexed = lex(&source).expect("source should lex");

    assert!(lexed.diagnostics.is_empty());
    assert_eq!(
        lexed
            .tokens
            .iter()
            .map(|token| (token.kind.clone(), spanned_text(&source, token.span)))
            .collect::<Vec<_>>(),
        vec![
            (TokenKind::Pub, "pub"),
            (TokenKind::Fn, "fn"),
            (TokenKind::Identifier("increment".into()), "increment"),
            (TokenKind::LeftParen, "("),
            (TokenKind::Identifier("value".into()), "value"),
            (TokenKind::Colon, ":"),
            (TokenKind::IntType, "Int"),
            (TokenKind::RightParen, ")"),
            (TokenKind::Arrow, "->"),
            (TokenKind::IntType, "Int"),
            (TokenKind::LeftBrace, "{"),
            (TokenKind::LineEnd, "\n"),
            (TokenKind::Identifier("value".into()), "value"),
            (TokenKind::Plus, "+"),
            (
                TokenKind::Integer(Integer::parse_decimal("1").expect("one is an integer")),
                "1",
            ),
            (TokenKind::LineEnd, "\n"),
            (TokenKind::RightBrace, "}"),
            (TokenKind::LineEnd, "\n"),
            (TokenKind::EndOfFile, ""),
        ]
    );

    let tree = parse(lexed);
    assert!(tree.lexical_diagnostics().is_empty());
    assert!(tree.parse_diagnostics().is_empty());
    let root = tree
        .root()
        .expect("the parser should retain one module root");
    assert_eq!(root.kind, NodeKind::Module);
    let [
        ConcreteElement::Node(definition_node),
        ConcreteElement::Token(line_end),
        ConcreteElement::Token(end_of_file),
    ] = root.children.as_slice()
    else {
        panic!("the module CST should contain one declaration and its boundaries");
    };
    assert_eq!(definition_node.kind, NodeKind::InlineOperationalGlobal);
    let [
        ConcreteElement::Token(public),
        ConcreteElement::Node(header),
        ConcreteElement::Node(body),
    ] = definition_node.children.as_slice()
    else {
        panic!("the operational CST should retain pub, its header, and its body");
    };
    assert_eq!(tree.tokens()[*public].kind, TokenKind::Pub);
    assert_eq!(header.kind, NodeKind::InlineOperationalHeader);
    assert_eq!(body.kind, NodeKind::Block);
    assert_eq!(tree.tokens()[*line_end].kind, TokenKind::LineEnd);
    assert_eq!(tree.tokens()[*end_of_file].kind, TokenKind::EndOfFile);
    assert_eq!(
        tree.events()
            .iter()
            .filter_map(|event| match event {
                Event::Start(kind) => Some(*kind),
                _ => None,
            })
            .filter(|kind| {
                matches!(
                    kind,
                    NodeKind::InlineOperationalGlobal | NodeKind::InlineOperationalHeader
                )
            })
            .collect::<Vec<_>>(),
        vec![
            NodeKind::InlineOperationalGlobal,
            NodeKind::InlineOperationalHeader,
        ]
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

    let module = project_module(&source, &tree).expect("public operational source should project");
    assert!(module.imports.is_empty());
    assert!(module.type_declarations.is_empty());
    let [definition] = module.definitions.as_slice() else {
        panic!("expected exactly one projected definition");
    };
    assert!(definition.public);
    assert_eq!(spanned_text(&source, definition.span), text.trim_end());
    let SurfaceDefinitionKind::InlineOperational(operational) = &definition.kind else {
        panic!("expected an inline operational definition");
    };
    assert_eq!(operational.header.name.text, "increment");
    assert_eq!(operational.header.parameters.len(), 1);
    assert!(matches!(
        operational.header.result_type.kind,
        SurfaceTypeKind::Int
    ));
    assert!(matches!(
        operational.body.result.kind,
        SurfaceExprKind::Add(_)
    ));
}

#[test]
fn projects_imports_visibility_and_a_declarations_only_root() {
    let module = parse_valid(
        "import @std.collections.list as List\nimport helpers.math (sum, Number as ImportedNumber)\n\npub opaque type Number = Number(Int)\n\npub main : Unit -> Int\nmain () = List.length (sum ())\n",
    );

    assert_eq!(module.imports.len(), 2);
    assert!(matches!(
        &module.imports[0].path,
        SurfaceModulePath::Absolute { root, segments }
            if root.text == "std"
                && segments.iter().map(|segment| segment.text.as_str()).collect::<Vec<_>>()
                    == ["collections", "list"]
    ));
    assert!(matches!(
        &module.imports[0].selection,
        SurfaceImportSelection::Qualified { alias } if alias.text == "List"
    ));
    assert!(matches!(
        &module.imports[1].path,
        SurfaceModulePath::Relative(segments)
            if segments.iter().map(|segment| segment.text.as_str()).collect::<Vec<_>>()
                == ["helpers", "math"]
    ));
    let SurfaceImportSelection::Targeted(items) = &module.imports[1].selection else {
        panic!("expected a targeted import");
    };
    assert_eq!(items.len(), 2);
    assert_eq!(items[0].name.text, "sum");
    assert!(items[0].alias.is_none());
    assert_eq!(items[1].name.text, "Number");
    assert_eq!(
        items[1].alias.as_ref().map(|alias| alias.text.as_str()),
        Some("ImportedNumber")
    );
    assert_eq!(module.type_declarations.len(), 1);
    assert_eq!(
        module.type_declarations[0].visibility,
        SurfaceTypeVisibility::PublicOpaque
    );
    assert_eq!(module.definitions.len(), 1);
    assert!(module.definitions[0].public);
}

#[test]
fn projects_qualified_occurrences_as_structured_references() {
    let text = "main : Data.Input<Int> -> Data.Output\nmain Data.Input = Ops.finish\n";
    let source = SourceFile::new("qualified.ash", text).expect("module source should fit");
    let tree = parse(lex(&source).expect("module source should lex"));
    let module = project_module(&source, &tree).expect("qualified references should project");
    let SurfaceDefinitionKind::Equational(definition) = &module.definitions[0].kind else {
        panic!("expected an equational definition");
    };
    let SurfaceTypeKind::Function(function) = &definition.interface.annotation.kind else {
        panic!("expected a function type");
    };
    let SurfaceTypeKind::Application {
        constructor: SurfaceReference::Qualified(domain),
        arguments,
    } = &function.domain.kind
    else {
        panic!("expected a qualified type application");
    };
    assert_eq!(domain.qualifier.text, "Data");
    assert_eq!(domain.member.text, "Input");
    assert_eq!(spanned_text(&source, domain.qualifier.span), "Data");
    assert_eq!(spanned_text(&source, domain.member.span), "Input");
    assert_eq!(spanned_text(&source, domain.span), "Data.Input");
    assert!(matches!(arguments[0].kind, SurfaceTypeKind::Int));
    let SurfaceTypeKind::Named(SurfaceReference::Qualified(codomain)) = &function.codomain.kind
    else {
        panic!("expected a qualified result type");
    };
    assert_eq!(spanned_text(&source, codomain.span), "Data.Output");

    let SurfacePatternKind::Constructor {
        name: SurfaceReference::Qualified(pattern),
        payload: None,
    } = &definition.equations[0].patterns[0].kind
    else {
        panic!("expected a qualified constructor pattern");
    };
    assert_eq!(pattern.qualifier.text, "Data");
    assert_eq!(pattern.member.text, "Input");
    assert_eq!(spanned_text(&source, pattern.span), "Data.Input");

    let SurfaceExprKind::Name(SurfaceReference::Qualified(body)) =
        &definition.equations[0].body.kind
    else {
        panic!("expected a qualified expression name");
    };
    assert_eq!(body.qualifier.text, "Ops");
    assert_eq!(body.member.text, "finish");
    assert_eq!(spanned_text(&source, body.span), "Ops.finish");
}

#[test]
fn accepts_private_and_public_transparent_declarations() {
    let module = parse_valid(
        "type Hidden = Hidden(Int)\n\npub type Visible = Visible(Int)\n\nmain : Unit -> Int\nmain () = 42\n",
    );

    assert_eq!(
        module.type_declarations[0].visibility,
        SurfaceTypeVisibility::Private
    );
    assert_eq!(
        module.type_declarations[1].visibility,
        SurfaceTypeVisibility::PublicTransparent
    );
    assert!(!module.definitions[0].public);
}

#[test]
fn rejects_a_file_result_after_module_declarations() {
    let source = SourceFile::new(
        "trailing-result.ash",
        "main : Unit -> Int\nmain () = 42\n\nmain ()\n",
    )
    .expect("source should fit");
    let tree = parse(lex(&source).expect("source should lex"));

    assert!(!tree.parse_diagnostics().is_empty());
}

#[test]
fn rejects_empty_targeted_imports_and_lowercase_full_import_aliases() {
    assert_parser_rejected("empty targeted import", "import math ()\n");
    assert_parser_rejected("lowercase full-import alias", "import math as lower\n");
}

#[test]
fn rejects_opaque_without_a_public_type_declaration() {
    assert_parser_rejected("private opaque type", "opaque type T = T(Int)\n");
    assert_parser_rejected(
        "opaque public function",
        "pub opaque fn main(value : Unit) -> Unit {\nvalue\n}\n",
    );
}

#[test]
fn rejects_imports_after_module_declarations() {
    assert_parser_rejected(
        "import after declaration",
        "type T = T(Int)\nimport math as Math\n",
    );
}

#[test]
fn rejects_malformed_absolute_module_paths() {
    let cases = [
        ("missing absolute-path descendant", "import @std as Std\n"),
        ("missing absolute-path root", "import @.list as List\n"),
        ("empty absolute-path segment", "import @std..list as List\n"),
        ("trailing absolute-path dot", "import @std.list. as List\n"),
    ];

    for (case, text) in cases {
        assert_parser_rejected(case, text);
    }
}

#[test]
fn malformed_relative_module_paths_retain_exact_parser_recovery() {
    let cases = [
        ("leading dot", "import .math as Math\n", ".", ".", 7, 8),
        ("trailing dot", "import math. as Math\n", "as", "as", 13, 15),
        (
            "empty internal segment",
            "import math..more as Math\n",
            ".",
            ".",
            12,
            13,
        ),
    ];

    for (case, import, offending_text, found, start, end) in cases {
        let text = format!("{import}main : Unit -> Int\nmain () = 0\n");
        let source = SourceFile::new("relative-path.ash", text).expect("source should fit");
        let lexed = lex(&source).expect("source should lex");
        assert!(
            lexed.diagnostics.is_empty(),
            "{case} should reach the parser"
        );
        let tree = parse(lexed);

        let [diagnostic] = tree.parse_diagnostics() else {
            panic!("{case} should produce exactly one parser diagnostic");
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{case}");
        assert_eq!(
            diagnostic.expected.as_deref(),
            Some("an identifier"),
            "{case}"
        );
        assert_eq!(diagnostic.found.as_deref(), Some(found), "{case}");
        assert_eq!(diagnostic.primary.span().range().start(), start, "{case}");
        assert_eq!(diagnostic.primary.span().range().end(), end, "{case}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            offending_text,
            "{case}"
        );
        assert!(diagnostic.related.is_empty(), "{case}");
        assert!(diagnostic.context.is_empty(), "{case}");

        let recovery = tree
            .events()
            .iter()
            .filter(|event| matches!(event, Event::Error(_) | Event::Missing { .. }))
            .collect::<Vec<_>>();
        assert!(
            matches!(
                recovery.as_slice(),
                [
                    Event::Error(ParseReason::ExpectedForm),
                    Event::Missing {
                        expected: ExpectedForm::Identifier,
                        at,
                    },
                ] if *at == diagnostic.primary.span()
            ),
            "{case}: {recovery:?}"
        );
        assert!(
            tree.events()
                .iter()
                .any(|event| matches!(event, Event::Start(NodeKind::EquationalGlobal))),
            "{case} should recover locally and parse the following declaration"
        );
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{case} should stop at the parser recovery boundary"
        );
    }
}

#[test]
fn rejects_qualifications_without_an_uppercase_module_alias() {
    assert_parser_rejected(
        "literal qualifier",
        "main : Unit -> Int\nmain () = 1.member\n",
    );
}

#[test]
fn malformed_qualified_members_retain_exact_parser_recovery() {
    let cases = [
        (
            "term trailing dot",
            "main : Unit -> Int\nmain () = Math.\n",
            &[(
                ParseReason::ExpectedForm,
                Some("an identifier"),
                Some("line end"),
                34,
                35,
            )][..],
            1,
        ),
        (
            "type trailing dot",
            "main : Math.\nmain _ = 0\n",
            &[(
                ParseReason::ExpectedForm,
                Some("an identifier"),
                Some("line end"),
                12,
                13,
            )][..],
            1,
        ),
        (
            "pattern trailing dot",
            "main : Unit -> Int\nmain Math. = 0\n",
            &[(
                ParseReason::ExpectedForm,
                Some("an identifier"),
                Some("="),
                30,
                31,
            )][..],
            1,
        ),
    ];

    for (case, text, expected, qualified_nodes) in cases {
        let source = SourceFile::new("qualified-member.ash", text).expect("source should fit");
        let lexed = lex(&source).expect("source should lex");
        assert!(
            lexed.diagnostics.is_empty(),
            "{case} should reach the parser"
        );
        let tree = parse(lexed);

        assert_exact_parser_diagnostics(case, &tree, expected);
        assert_eq!(
            tree.events()
                .iter()
                .filter(|event| matches!(event, Event::Start(NodeKind::QualifiedName)))
                .count(),
            qualified_nodes,
            "{case}"
        );
        assert!(
            tree.events()
                .iter()
                .any(|event| matches!(event, Event::Error(_))),
            "{case} should retain its error in the CST"
        );
        assert_eq!(
            tree.events()
                .iter()
                .filter_map(|event| match event {
                    Event::Token(index) => Some(*index),
                    _ => None,
                })
                .collect::<Vec<_>>(),
            (0..tree.tokens().len()).collect::<Vec<_>>(),
            "{case} should retain every lexer token"
        );
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{case} should stop at the parser recovery boundary"
        );
    }
}

#[test]
fn lowercase_qualifiers_never_enter_the_qualified_name_grammar() {
    let cases = [
        (
            "term qualifier",
            "main : Unit -> Int\nmain () = lower.member\n",
            &[(
                ParseReason::UnexpectedToken,
                None,
                Some("identifier"),
                29,
                34,
            )][..],
        ),
        (
            "type qualifier",
            "main : lower.Member -> Int\nmain _ = 0\n",
            &[(
                ParseReason::UnexpectedToken,
                None,
                Some("identifier"),
                7,
                12,
            )][..],
        ),
        (
            "pattern qualifier",
            "main : Unit -> Int\nmain lower.Member = 0\n",
            &[(
                ParseReason::UnexpectedToken,
                None,
                Some("identifier"),
                24,
                29,
            )][..],
        ),
    ];

    for (case, text, expected) in cases {
        let source = SourceFile::new("lowercase-qualifier.ash", text).expect("source should fit");
        let tree = parse(lex(&source).expect("source should lex"));

        assert_exact_parser_diagnostics(case, &tree, expected);
        assert!(
            !tree
                .events()
                .iter()
                .any(|event| matches!(event, Event::Start(NodeKind::QualifiedName))),
            "{case} must not enter the qualified-name grammar"
        );
        assert!(
            tree.events()
                .iter()
                .any(|event| matches!(event, Event::Error(_))),
            "{case} should retain parser recovery"
        );
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{case} should stop at the parser recovery boundary"
        );
    }
}
