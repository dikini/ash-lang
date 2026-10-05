use ash::{
    lexer::{TokenKind, lex},
    parser::{parse, project_module},
    source::SourceFile,
    surface::{SurfaceDefinitionKind, SurfaceExprKind, SurfaceTypeKind},
};

#[test]
fn strings_decode_utf8_and_each_supported_escape_with_exact_spans() {
    for (literal, expected) in [
        (r#""""#, ""),
        (r#""héllo 世界""#, "héllo 世界"),
        (r#""\"\\\n\r\t\0""#, "\"\\\n\r\t\0"),
        (r#""// /* Int { (""#, "// /* Int { ("),
    ] {
        let source = SourceFile::new("string.ash", literal).unwrap();
        let lexed = lex(&source).unwrap();
        assert!(lexed.diagnostics.is_empty(), "{literal:?}");
        assert_eq!(
            lexed.tokens[0].kind,
            TokenKind::StringLiteral(expected.into())
        );
        assert_eq!(lexed.tokens[0].span.range().start(), 0);
        assert_eq!(lexed.tokens[0].span.range().end() as usize, literal.len());
    }
}

#[test]
fn malformed_strings_reject_without_surface_projection() {
    for literal in [
        "\"unterminated",
        "\"trailing\\",
        r#""\q""#,
        r#""\u1234""#,
        r#""\x41""#,
        "\"physical\nnewline\"",
        "\"physical\r\nnewline\"",
        "\"physical\rreturn\"",
        "\"raw\ttab\"",
        "\"raw\0nul\"",
        "\"raw\u{7f}del\"",
    ] {
        let source = SourceFile::new("invalid-string.ash", literal).unwrap();
        let lexed = lex(&source).unwrap();
        assert!(!lexed.diagnostics.is_empty(), "{literal:?}");
        assert!(lexed.resource_failure().is_none());
        let tree = parse(lexed);
        assert!(project_module(&source, &tree).is_err(), "{literal:?}");
    }
}

#[test]
fn string_expression_and_builtin_types_project_through_the_cst() {
    let source = SourceFile::new(
        "string.ash",
        "main : Bytes -> String\nmain bytes = \"世界\\n\"\n",
    )
    .unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(tree.lexical_diagnostics().is_empty());
    assert!(tree.parse_diagnostics().is_empty());
    let module = project_module(&source, &tree).unwrap();
    let SurfaceDefinitionKind::Equational(main) = &module.definitions[0].kind else {
        panic!("equational")
    };
    let SurfaceTypeKind::Function(annotation) = &main.interface.annotation.kind else {
        panic!("function")
    };
    assert_eq!(annotation.domain.kind, SurfaceTypeKind::Bytes);
    assert_eq!(annotation.codomain.kind, SurfaceTypeKind::String);
    let expression = &main.equations[0].body;
    assert_eq!(expression.kind, SurfaceExprKind::String("世界\n".into()));
    let range = expression.span.range();
    assert_eq!(
        &source.text()[range.start() as usize..range.end() as usize],
        "\"世界\\n\""
    );
}

#[test]
fn strings_remain_expression_only_and_builtin_types_have_no_arguments() {
    for text in [
        "main : String -> Int\nmain \"value\" = 1\n",
        "main : Unit -> String<Int>\nmain () = \"value\"\n",
        "main : Bytes<Int> -> Unit\nmain value = ()\n",
    ] {
        let source = SourceFile::new("invalid-string-syntax.ash", text).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(tree.lexical_diagnostics().is_empty());
        assert!(!tree.parse_diagnostics().is_empty(), "{text}");
        assert!(project_module(&source, &tree).is_err());
    }
}

#[test]
fn unicode_identifiers_remain_excluded() {
    for text in ["café", "世界"] {
        let source = SourceFile::new(
            "excluded.ash",
            format!("main : Unit -> String\nmain () = {text}\n"),
        )
        .unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(project_module(&source, &tree).is_err(), "{text}");
    }
}

#[test]
fn byte_prefix_is_an_ordinary_identifier_followed_by_a_string() {
    let source = SourceFile::new("adjacency.ash", "b\"bytes\"").unwrap();
    let lexed = lex(&source).unwrap();
    assert!(lexed.diagnostics.is_empty());
    assert_eq!(lexed.tokens[0].kind, TokenKind::Identifier("b".into()));
    assert_eq!(
        lexed.tokens[1].kind,
        TokenKind::StringLiteral("bytes".into())
    );
}

#[test]
fn malformed_strings_have_structured_reasons_and_render_in_both_locales() {
    use ash::{
        lexer::LexReason,
        message::{Catalogue, Locale, Message},
    };
    for (literal, reason, message) in [
        (
            r#""\q""#,
            LexReason::InvalidStringEscape,
            Message::lex_invalid_string_escape(),
        ),
        (
            "\"unfinished",
            LexReason::UnterminatedString,
            Message::lex_unterminated_string(),
        ),
        (
            "\"line\nbreak\"",
            LexReason::InvalidStringCharacter,
            Message::lex_invalid_string_character(),
        ),
    ] {
        let source = SourceFile::new("reason.ash", literal).unwrap();
        let lexed = lex(&source).unwrap();
        assert_eq!(lexed.diagnostics.len(), 1);
        assert_eq!(lexed.diagnostics[0].reason, reason);
        assert_eq!(lexed.diagnostics[0].primary.span().range().start(), 0);
        assert_eq!(
            lexed.diagnostics[0].primary.span().range().end() as usize,
            literal.len()
        );
        for locale in [Locale::English, Locale::Bulgarian] {
            assert!(
                !Catalogue::new(locale)
                    .unwrap()
                    .format(&message)
                    .unwrap()
                    .is_empty()
            );
        }
    }
}
