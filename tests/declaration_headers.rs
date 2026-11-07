use std::path::PathBuf;

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    lexer::lex,
    module::ModuleRoots,
    parser::{ConcreteElement, Event, NodeKind, ProjectionError, parse, project_module},
    source::{SourceFile, Span},
    surface::{
        SurfaceSyntaxCaptureKind, SurfaceSyntaxCategory, SurfaceSyntaxImplementation,
        SurfaceSyntaxMatcherPart,
    },
};

fn fixture(directory: &str, name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures")
            .join(directory)
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

fn parsed(text: &str) -> (SourceFile, ash::parser::ConcreteTree) {
    let source = SourceFile::new("headers.ash", text).unwrap();
    let lexed = lex(&source).unwrap();
    assert!(lexed.diagnostics.is_empty(), "{:?}", lexed.diagnostics);
    let tree = parse(lexed);
    assert_eq!(
        tree.events()
            .iter()
            .filter_map(|event| match event {
                Event::Token(index) => Some(*index),
                _ => None,
            })
            .collect::<Vec<_>>(),
        (0..tree.tokens().len()).collect::<Vec<_>>(),
        "the concrete tree must retain each token exactly once"
    );
    (source, tree)
}

fn text_at(source: &SourceFile, span: Span) -> &str {
    let range = span.range();
    &source.text()[range.start() as usize..range.end() as usize]
}

#[test]
fn projects_declaration_headers_with_template_and_transformer() {
    let text = format!(
        "{}pub syntax declaration: (computed) => using expand_computed\n",
        include_str!("../docs/design/macros/fixtures/header_compat/forms.ash")
    );
    let (source, tree) = parsed(&text);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).unwrap();
    let declaration = tree
        .root()
        .unwrap()
        .children
        .iter()
        .find_map(|element| match element {
            ConcreteElement::Node(node) if node.kind == NodeKind::SyntaxDeclaration => Some(node),
            _ => None,
        })
        .unwrap();
    let body = declaration
        .children
        .iter()
        .find_map(|element| match element {
            ConcreteElement::Node(node) if node.kind == NodeKind::TemplateBody => Some(node),
            _ => None,
        })
        .unwrap();
    let (Some(ConcreteElement::Token(first)), Some(ConcreteElement::Token(last))) =
        (body.children.first(), body.children.last())
    else {
        panic!("template body should retain its delimiters");
    };
    let body_start = tree.tokens()[*first].span.range().start() as usize;
    let body_end = tree.tokens()[*last].span.range().end() as usize;
    assert_eq!(
        &text[body_start..body_end],
        "{\n    pub $name : Unit -> Int\n    $name () = 42\n}"
    );
    let [template, transformer] = module.syntax_declarations.as_slice() else {
        panic!("expected two syntax definitions");
    };
    assert_eq!(template.name.text, "make_value");
    assert_eq!(template.category, SurfaceSyntaxCategory::Declaration);
    assert_eq!(text_at(&source, template.name.span), "make_value");
    assert_eq!(
        text_at(&source, template.span),
        text.lines().take(4).collect::<Vec<_>>().join("\n")
    );
    assert!(matches!(
        &template.matcher[..],
        [SurfaceSyntaxMatcherPart::Capture { name, kind: SurfaceSyntaxCaptureKind::Identifier }]
            if name.text == "name" && text_at(&source, name.span) == "name"
    ));
    assert!(matches!(
        template.implementation,
        SurfaceSyntaxImplementation::Template
    ));
    assert_eq!(transformer.name.text, "computed");
    assert_eq!(transformer.category, SurfaceSyntaxCategory::Declaration);
    assert!(transformer.matcher.is_empty());
    assert!(matches!(
        &transformer.implementation,
        SurfaceSyntaxImplementation::Transformer(name)
            if name.text == "expand_computed" && text_at(&source, name.span) == "expand_computed"
    ));
}

#[test]
fn projects_existing_expression_headers_without_changing_their_category() {
    for (text, name, literals) in [
        (
            include_str!("../docs/design/macros/fixtures/header_compat/expressions.ash"),
            "declaration",
            &[":", "foo"][..],
        ),
        (
            include_str!("../docs/design/macros/fixtures/header_compat/derive_expressions.ash"),
            "derive",
            &["marker"][..],
        ),
    ] {
        let (source, tree) = parsed(text);
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
        let module = project_module(&source, &tree).unwrap();
        let declaration = &module.syntax_declarations[0];
        assert_eq!(declaration.category, SurfaceSyntaxCategory::Expression);
        assert_eq!(declaration.name.text, name);
        assert_eq!(text_at(&source, declaration.name.span), name);
        assert_eq!(text_at(&source, declaration.span), text.trim_end());
        assert_eq!(
            declaration
                .matcher
                .iter()
                .filter_map(|part| match part {
                    SurfaceSyntaxMatcherPart::Literal { spelling, .. } => Some(spelling.as_str()),
                    _ => None,
                })
                .collect::<Vec<_>>(),
            literals
        );
        assert!(
            matches!(declaration.matcher.last(), Some(SurfaceSyntaxMatcherPart::Capture {
            name, kind: SurfaceSyntaxCaptureKind::Expression
        }) if name.text == "value")
        );
    }
}

#[test]
fn malformed_declaration_headers_stop_at_recovery_boundary() {
    for text in [
        "pub syntax declaration: () => {}\n",
        "pub syntax declaration: (Name) => {}\n",
        "pub syntax declaration: (syntax) => {}\n",
        "pub syntax declaration: (name => {}\n",
        "pub syntax declaration: (name, other) => {}\n",
        "pub syntax declaration (name) => {}\n",
    ] {
        let (source, tree) = parsed(text);
        assert!(!tree.parse_diagnostics().is_empty(), "accepted {text:?}");
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{text:?}"
        );
    }
}

#[test]
fn reserved_syntax_is_rejected_in_user_identifier_positions() {
    for text in [
        include_str!("../docs/design/macros/fixtures/escapes/reserved_term.ash"),
        include_str!("../docs/design/macros/fixtures/escapes/reserved_macro.ash"),
        include_str!("../docs/design/macros/fixtures/escapes/reserved_module.ash"),
        include_str!("../docs/design/macros/fixtures/escapes/reserved_alias.ash"),
        "import macros (syntax choose as syntax)\n",
        "import macros (syntax syntax)\n",
        "import thing.syntax as Thing\n",
        "import @syntax.thing as Thing\n",
        "import @builtin.syntax as Thing\n",
        "import @other.compiler.syntax as Thing\n",
        "import @builtin.compiler.syntax.more as Thing\n",
        "import thing as syntax\n",
        "f : Int -> Int\nf syntax = syntax\n",
        "pub syntax form $syntax:expr => { $syntax }\n",
    ] {
        let (source, tree) = parsed(text);
        assert!(!tree.parse_diagnostics().is_empty(), "accepted {text:?}");
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{text:?}"
        );
    }
}

#[test]
fn fixed_header_and_reservation_fixtures_run_through_the_driver() {
    for (directory, name) in [
        ("header_compat", "compat.ash"),
        ("header_compat", "derive_compat.ash"),
        ("escapes", "reserved_control.ash"),
    ] {
        let compiled = compile_path(fixture(directory, name)).expect(name);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{name}");
    }
    for name in [
        "reserved_term.ash",
        "reserved_macro.ash",
        "reserved_module.ash",
        "reserved_alias.ash",
    ] {
        compile_path(fixture("escapes", name)).expect_err(name);
    }
}

#[test]
fn declaration_headers_are_not_admitted_by_the_expression_driver() {
    compile_path(fixture("header_compat", "forms.ash"))
        .expect_err("declaration admission is a later delivery");
}
