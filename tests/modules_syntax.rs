use ash::{
    lexer::{TokenKind, lex},
    parser::{NodeKind, ProjectionError, parse, project_module},
    source::SourceFile,
    surface::{
        SurfaceDefinitionKind, SurfaceExprKind, SurfaceImportSelection, SurfaceModulePath,
        SurfacePatternKind, SurfaceReference, SurfaceTypeKind, SurfaceTypeVisibility,
    },
};

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

#[test]
fn modular_reserved_words_and_path_punctuation_are_closed_tokens() {
    let source = SourceFile::new(
        "tokens.ash",
        "import @std.collections.list as List\npub opaque type T = T(Int)\n",
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
fn rejects_qualifications_without_an_uppercase_module_alias() {
    assert_parser_rejected(
        "lowercase qualifier",
        "main : Unit -> Int\nmain () = lower.member\n",
    );
    assert_parser_rejected(
        "literal qualifier",
        "main : Unit -> Int\nmain () = 1.member\n",
    );
}
