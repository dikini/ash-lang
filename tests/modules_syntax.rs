use ash::{
    integer::Integer,
    lexer::{TokenKind, lex},
    parser::{
        ConcreteElement, Event, ExpectedForm, NodeKind, ParseContext, ParseReason, ProjectionError,
        SynchronizationBoundary, parse, project_module,
    },
    source::{ByteRange, SourceFile},
    surface::{
        SurfaceDeclarationIndex, SurfaceDefinitionKind, SurfaceExprKind, SurfaceImportItem,
        SurfaceImportSelection, SurfaceKindKind, SurfaceModulePath, SurfaceNominalDeclarationKind,
        SurfacePatternKind, SurfaceReference, SurfaceTypeKind, SurfaceTypeVisibility,
    },
};

type ExpectedParserDiagnostic<'a> = (ParseReason, Option<&'a str>, Option<&'a str>, u32, u32);

fn parse_valid(text: &str) -> ash::surface::SurfaceModule {
    let source = SourceFile::new("module.ash", text).expect("module source should fit");
    parse_valid_source(&source)
}

fn parse_valid_source(source: &SourceFile) -> ash::surface::SurfaceModule {
    let lexed = lex(source).expect("module source should lex");
    assert!(lexed.diagnostics.is_empty(), "{:?}", lexed.diagnostics);
    let tree = parse(lexed);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert_eq!(tree.root().map(|root| root.kind), Some(NodeKind::Module));
    project_module(source, &tree).expect("module source should project")
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

fn assert_token_complete(case: &str, tree: &ash::parser::ConcreteTree) {
    assert_eq!(
        tree.events()
            .iter()
            .filter_map(|event| match event {
                Event::Token(index) => Some(*index),
                _ => None,
            })
            .collect::<Vec<_>>(),
        (0..tree.tokens().len()).collect::<Vec<_>>(),
        "{case} should retain every lexer token exactly once"
    );
}

fn assert_balanced_events(case: &str, tree: &ash::parser::ConcreteTree) {
    let mut depth = 0_u32;
    for event in tree.events() {
        match event {
            Event::Start(_) => depth += 1,
            Event::Finish => {
                assert!(depth > 0, "{case} has an unmatched finish");
                depth -= 1;
            }
            Event::Token(_) | Event::Missing { .. } | Event::Error(_) => {}
        }
    }
    assert_eq!(depth, 0, "{case} should retain balanced events");
}

#[test]
fn modular_reserved_words_and_path_punctuation_are_closed_tokens() {
    let source = SourceFile::new(
        "tokens.ash",
        "import @std.collections.list as List\npub opaque type T = T(Int)\nnewtype N = N(Int)\ninterface impl where\n",
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
            .any(|token| token.kind == TokenKind::Newtype)
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
fn module_newtype_projects_same_spelled_one_field_representation() {
    let text = "pub opaque newtype UserId = UserId(Int)\n";
    let source = SourceFile::new("newtype.ash", text).expect("newtype source should fit");
    let lexed = lex(&source).expect("newtype source should lex");

    assert!(lexed.diagnostics.is_empty());
    assert!(
        lexed
            .tokens
            .iter()
            .any(|token| token.kind == TokenKind::Newtype
                && spanned_text(&source, token.span) == "newtype"),
        "{:?}",
        lexed.tokens
    );

    let tree = parse(lexed);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert!(
        tree.events()
            .iter()
            .any(|event| matches!(event, Event::Start(NodeKind::NewtypeDeclaration))),
        "{:?}",
        tree.events()
    );

    let module = project_module(&source, &tree).expect("newtype source should project");
    assert!(module.imports.is_empty());
    assert_eq!(
        module.declaration_order,
        vec![SurfaceDeclarationIndex::Type(0)]
    );
    let [declaration] = module.type_declarations.as_slice() else {
        panic!("expected one projected nominal declaration");
    };
    assert_eq!(
        declaration.declaration_kind,
        SurfaceNominalDeclarationKind::Newtype
    );
    assert_eq!(declaration.visibility, SurfaceTypeVisibility::PublicOpaque);
    assert_eq!(declaration.name.text, "UserId");
    assert_eq!(spanned_text(&source, declaration.name.span), "UserId");
    assert!(declaration.parameters.is_empty());
    let [constructor] = declaration.constructors.as_slice() else {
        panic!("expected one newtype constructor");
    };
    assert_eq!(constructor.name.text, "UserId");
    assert_eq!(spanned_text(&source, constructor.name.span), "UserId");
    let [field] = constructor.fields.as_slice() else {
        panic!("expected one representation field");
    };
    assert!(matches!(field.kind, SurfaceTypeKind::Int));
    assert_eq!(spanned_text(&source, field.span), "Int");
    assert_eq!(spanned_text(&source, declaration.span), text.trim_end());
}

#[test]
fn reserved_newtype_spelling_cannot_be_used_as_a_value_identifier() {
    let text = "main : Unit -> Int\nmain () = newtype\n";
    let source =
        SourceFile::new("reserved-newtype.ash", text).expect("reserved-newtype source should fit");
    let lexed = lex(&source).expect("reserved-newtype source should lex");
    assert!(lexed.diagnostics.is_empty(), "{:?}", lexed.diagnostics);
    assert!(lexed.tokens.iter().any(|token| {
        token.kind == TokenKind::Newtype && spanned_text(&source, token.span) == "newtype"
    }));

    let tree = parse(lexed);
    let [diagnostic] = tree.parse_diagnostics() else {
        panic!(
            "the reserved spelling should have one owned parser diagnostic: {:?}",
            tree.parse_diagnostics()
        );
    };
    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(diagnostic.expected.as_deref(), Some("an expression"));
    assert_eq!(diagnostic.found.as_deref(), Some("newtype"));
    assert_eq!(spanned_text(&source, diagnostic.primary.span()), "newtype");
    assert_token_complete("reserved newtype value identifier", &tree);
    assert_balanced_events("reserved newtype value identifier", &tree);
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn module_newtype_projects_visibility_kinded_parameters_and_distinct_constructor_spelling() {
    let text = "newtype PrivateId = PrivateId(Int)\n\npub newtype PublicId = PublicId(Int)\n\npub opaque newtype OpaqueId = OpaqueId(Int)\n\npub newtype Wrapped<F : Type -> Type, A> = Wraps(F<A>)\n\npub type Box = Box(Int)\n";
    let source = SourceFile::new("newtypes.ash", text).expect("newtype source should fit");
    let module = parse_valid_source(&source);

    assert_eq!(
        module.declaration_order,
        vec![
            SurfaceDeclarationIndex::Type(0),
            SurfaceDeclarationIndex::Type(1),
            SurfaceDeclarationIndex::Type(2),
            SurfaceDeclarationIndex::Type(3),
            SurfaceDeclarationIndex::Type(4),
        ]
    );
    assert_eq!(
        module
            .type_declarations
            .iter()
            .map(|declaration| declaration.declaration_kind)
            .collect::<Vec<_>>(),
        vec![
            SurfaceNominalDeclarationKind::Newtype,
            SurfaceNominalDeclarationKind::Newtype,
            SurfaceNominalDeclarationKind::Newtype,
            SurfaceNominalDeclarationKind::Newtype,
            SurfaceNominalDeclarationKind::Data,
        ]
    );
    assert_eq!(
        module
            .type_declarations
            .iter()
            .map(|declaration| declaration.visibility)
            .collect::<Vec<_>>(),
        vec![
            SurfaceTypeVisibility::Private,
            SurfaceTypeVisibility::PublicTransparent,
            SurfaceTypeVisibility::PublicOpaque,
            SurfaceTypeVisibility::PublicTransparent,
            SurfaceTypeVisibility::PublicTransparent,
        ]
    );

    let wrapped = &module.type_declarations[3];
    assert_eq!(wrapped.name.text, "Wrapped");
    assert_eq!(
        spanned_text(&source, wrapped.span),
        "pub newtype Wrapped<F : Type -> Type, A> = Wraps(F<A>)"
    );
    let [constructor] = wrapped.constructors.as_slice() else {
        panic!("expected one projected constructor");
    };
    assert_eq!(constructor.name.text, "Wraps");
    assert_eq!(spanned_text(&source, constructor.span), "Wraps(F<A>)");
    let [higher, element] = wrapped.parameters.as_slice() else {
        panic!("expected two newtype type parameters");
    };
    assert_eq!(higher.name.text, "F");
    let kind = higher
        .kind
        .as_ref()
        .expect("F should have a kind annotation");
    let SurfaceKindKind::Function { domain, codomain } = &kind.kind else {
        panic!("expected a function kind");
    };
    assert!(matches!(domain.kind, SurfaceKindKind::Type));
    assert!(matches!(codomain.kind, SurfaceKindKind::Type));
    assert_eq!(element.name.text, "A");
    assert!(element.kind.is_none());
    let [field] = constructor.fields.as_slice() else {
        panic!("expected the one representation field");
    };
    let SurfaceTypeKind::Application {
        constructor: representation_constructor,
        arguments,
    } = &field.kind
    else {
        panic!("expected the representation field to retain F<A>");
    };
    assert_eq!(representation_constructor.member().text, "F");
    let [argument] = arguments.as_slice() else {
        panic!("expected one type argument");
    };
    assert!(matches!(
        &argument.kind,
        SurfaceTypeKind::Named(SurfaceReference::Unqualified(name)) if name.text == "A"
    ));

    let ordinary = &module.type_declarations[4];
    assert_eq!(ordinary.name.text, "Box");
    assert_eq!(
        ordinary.declaration_kind,
        SurfaceNominalDeclarationKind::Data
    );
}

#[test]
fn malformed_module_newtypes_recover_with_token_complete_following_declarations() {
    let cases = [
        (
            "missing constructor",
            "newtype Missing =\nmain : Unit -> Int\nmain () = 0\n",
            ParseReason::ExpectedForm,
            Some("an identifier"),
            Some("line end"),
            17,
            18,
            "\n",
            None,
        ),
        (
            "nullary constructor",
            "newtype Empty = Empty\nmain : Unit -> Int\nmain () = 0\n",
            ParseReason::ExpectedForm,
            Some("("),
            Some("line end"),
            21,
            22,
            "\n",
            None,
        ),
        (
            "missing representation field",
            "newtype Empty = Empty()\nmain : Unit -> Int\nmain () = 0\n",
            ParseReason::ExpectedForm,
            Some("a type"),
            Some(")"),
            22,
            23,
            ")",
            None,
        ),
        (
            "second field",
            "newtype Pair = Pair(Int, Int)\nmain : Unit -> Int\nmain () = 0\n",
            ParseReason::ExpectedForm,
            Some(")"),
            Some(","),
            23,
            24,
            ",",
            Some((SynchronizationBoundary::ParenthesisClosing, 28, 29)),
        ),
        (
            "second constructor",
            "newtype Choice = Choice(Int)\n| Other(Int)\nmain : Unit -> Int\nmain () = 0\n",
            ParseReason::ExpectedForm,
            Some("a logical line end"),
            Some("|"),
            29,
            30,
            "|",
            Some((SynchronizationBoundary::LogicalLineEnd, 41, 42)),
        ),
    ];

    for (case, text, reason, expected, found, start, end, offending, synchronization) in cases {
        let source = SourceFile::new("malformed-newtype.ash", text)
            .expect("malformed newtype source should fit");
        let lexed = lex(&source).expect("malformed newtype source should lex");
        assert!(
            lexed.diagnostics.is_empty(),
            "{case}: {:?}",
            lexed.diagnostics
        );
        let tree = parse(lexed);

        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{case} should retain exactly one parser diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, reason, "{case}");
        assert_eq!(diagnostic.expected.as_deref(), expected, "{case}");
        assert_eq!(diagnostic.found.as_deref(), found, "{case}");
        assert_eq!(diagnostic.primary.span().range().start(), start, "{case}");
        assert_eq!(diagnostic.primary.span().range().end(), end, "{case}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            offending,
            "{case}"
        );
        if let Some((boundary, sync_start, sync_end)) = synchronization {
            let [
                ParseContext::Synchronization {
                    boundary: actual,
                    span,
                },
            ] = diagnostic.context.as_slice()
            else {
                panic!("{case} should retain one synchronization context");
            };
            assert_eq!(*actual, boundary, "{case}");
            assert_eq!(span.source(), source.id(), "{case}");
            assert_eq!(span.range().start(), sync_start, "{case}");
            assert_eq!(span.range().end(), sync_end, "{case}");
            let [related] = diagnostic.related.as_slice() else {
                panic!("{case} should retain one synchronization label");
            };
            assert_eq!(related.span().source(), source.id(), "{case}");
            assert_eq!(related.span().range().start(), sync_start, "{case}");
            assert_eq!(related.span().range().end(), sync_end, "{case}");
        }
        assert!(
            tree.events()
                .iter()
                .any(|event| matches!(event, Event::Start(NodeKind::NewtypeDeclaration))),
            "{case} should enter the newtype declaration grammar"
        );
        assert!(
            tree.events()
                .iter()
                .any(|event| matches!(event, Event::Start(NodeKind::EquationalGlobal))),
            "{case} should parse the following valid declaration"
        );
        assert_token_complete(case, &tree);
        assert_balanced_events(case, &tree);
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{case} should stop at parser recovery before projection"
        );
    }
}

#[test]
fn module_newtype_missing_right_delimiter_reports_causal_opening_and_retains_tokens() {
    let text = "newtype Broken = Broken(Int\nmain : Unit -> Int\nmain () = 0\n";
    let source = SourceFile::new("malformed-newtype.ash", text)
        .expect("malformed newtype source should fit");
    let lexed = lex(&source).expect("malformed newtype source should lex");
    assert!(lexed.diagnostics.is_empty(), "{:?}", lexed.diagnostics);
    let tree = parse(lexed);

    let [unclosed, boundary] = tree.parse_diagnostics() else {
        panic!(
            "missing right delimiter should retain two parser diagnostics: {:?}",
            tree.parse_diagnostics()
        );
    };
    assert_eq!(unclosed.reason, ParseReason::UnclosedGroup);
    assert_eq!(unclosed.expected.as_deref(), Some(")"));
    assert_eq!(unclosed.found.as_deref(), Some("identifier"));
    assert_eq!(spanned_text(&source, unclosed.primary.span()), "(");
    assert_eq!(unclosed.primary.span().range().start(), 23);
    assert_eq!(unclosed.primary.span().range().end(), 24);
    let [related] = unclosed.related.as_slice() else {
        panic!("the unclosed group should point at the next retained token");
    };
    assert_eq!(spanned_text(&source, related.span()), "main");
    assert_eq!(related.span().range().start(), 28);
    assert_eq!(related.span().range().end(), 32);
    assert!(unclosed.context.is_empty());

    assert_eq!(boundary.reason, ParseReason::ExpectedForm);
    assert_eq!(boundary.expected.as_deref(), Some("a logical line end"));
    assert_eq!(boundary.found.as_deref(), Some("identifier"));
    assert_eq!(spanned_text(&source, boundary.primary.span()), "main");
    assert_eq!(boundary.primary.span().range().start(), 28);
    assert_eq!(boundary.primary.span().range().end(), 32);
    assert!(boundary.related.is_empty());
    assert!(boundary.context.is_empty());

    assert!(
        tree.events()
            .iter()
            .any(|event| matches!(event, Event::Start(NodeKind::NewtypeDeclaration)))
    );
    assert_token_complete("missing right delimiter", &tree);
    assert_balanced_events("missing right delimiter", &tree);
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
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
    assert!(matches!(
        &items[0],
        SurfaceImportItem::Name { name, alias: None, .. } if name.text == "sum"
    ));
    assert!(matches!(
        &items[1],
        SurfaceImportItem::Name { name, alias: Some(alias), .. }
            if name.text == "Number" && alias.text == "ImportedNumber"
    ));
    assert_eq!(module.type_declarations.len(), 1);
    assert_eq!(
        module.type_declarations[0].visibility,
        SurfaceTypeVisibility::PublicOpaque
    );
    assert_eq!(module.definitions.len(), 1);
    assert!(module.definitions[0].public);
}

#[test]
fn projects_public_imports_and_independent_selector_channels() {
    let text = "pub import equality (Equal as Equality, equal, impl Equal)\n";
    let source = SourceFile::new("public-import.ash", text).expect("module source should fit");
    let module = parse_valid_source(&source);

    let [import] = module.imports.as_slice() else {
        panic!("expected exactly one import");
    };
    assert!(import.public);
    let SurfaceImportSelection::Targeted(items) = &import.selection else {
        panic!("expected a targeted import");
    };
    let [first, second, third] = items.as_slice() else {
        panic!("expected three import selectors");
    };
    let SurfaceImportItem::Name {
        name: first_name,
        alias: Some(first_alias),
        span: first_span,
    } = first
    else {
        panic!("expected the first selector to rename Equal");
    };
    assert_eq!(first_name.text, "Equal");
    assert_eq!(first_name.span.source(), source.id());
    assert_eq!(
        first_name.span.range(),
        ByteRange::new(21, 26).expect("the Equal range is ordered")
    );
    assert_eq!(first_alias.text, "Equality");
    assert_eq!(first_alias.span.source(), source.id());
    assert_eq!(
        first_alias.span.range(),
        ByteRange::new(30, 38).expect("the Equality range is ordered")
    );
    assert_eq!(first_span.source(), source.id());
    assert_eq!(
        first_span.range(),
        ByteRange::new(21, 38).expect("the renamed selector range is ordered")
    );

    let SurfaceImportItem::Name {
        name: second_name,
        alias: None,
        span: second_span,
    } = second
    else {
        panic!("expected the second selector to name equal");
    };
    assert_eq!(second_name.text, "equal");
    assert_eq!(second_name.span.source(), source.id());
    assert_eq!(
        second_name.span.range(),
        ByteRange::new(40, 45).expect("the equal range is ordered")
    );
    assert_eq!(second_span.source(), source.id());
    assert_eq!(
        second_span.range(),
        ByteRange::new(40, 45).expect("the selector range is ordered")
    );

    let SurfaceImportItem::Implementation {
        interface,
        span: implementation_span,
    } = third
    else {
        panic!("expected the third selector to select Equal implementations");
    };
    assert_eq!(interface.text, "Equal");
    assert_eq!(interface.span.source(), source.id());
    assert_eq!(
        interface.span.range(),
        ByteRange::new(52, 57).expect("the implementation Equal range is ordered")
    );
    assert_eq!(implementation_span.source(), source.id());
    assert_eq!(
        implementation_span.range(),
        ByteRange::new(47, 57).expect("the implementation selector range is ordered")
    );
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
    assert_parser_rejected(
        "public import after declaration",
        "type T = T(Int)\npub import math (Value)\n",
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
