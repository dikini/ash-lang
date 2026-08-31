use ash::{
    lexer::{LexReason, Token, TokenKind, lex},
    parser::{ResourceFailure, SYNTAX_WORK_LIMIT},
    source::SourceFile,
};

fn token_kinds(source: &SourceFile) -> Vec<TokenKind> {
    let lexed = lex(source).expect("the admitted source should remain representable while lexing");
    assert!(
        lexed.diagnostics.is_empty(),
        "valid test input produced diagnostics: {:?}",
        lexed.diagnostics
    );
    lexed.tokens.into_iter().map(|token| token.kind).collect()
}

#[test]
fn recognizes_recursion_reserved_words() {
    let source = SourceFile::new("recursion-words.ash", "rec and record android")
        .expect("the token source should fit");

    assert_eq!(
        token_kinds(&source),
        vec![
            TokenKind::Rec,
            TokenKind::And,
            TokenKind::Identifier("record".into()),
            TokenKind::Identifier("android".into()),
            TokenKind::EndOfFile,
        ]
    );
}

#[test]
fn recognizes_interface_reserved_words_without_stealing_identifier_boundaries() {
    let source = SourceFile::new(
        "interface-keywords.ash",
        "interface impl where interface_ implement whereupon",
    )
    .expect("the keyword fixture should fit");
    let lexed = lex(&source).expect("the keyword fixture should lex");
    let expected = [
        (TokenKind::Interface, 0, 9),
        (TokenKind::Impl, 10, 14),
        (TokenKind::Where, 15, 20),
        (TokenKind::Identifier("interface_".into()), 21, 31),
        (TokenKind::Identifier("implement".into()), 32, 41),
        (TokenKind::Identifier("whereupon".into()), 42, 51),
        (TokenKind::EndOfFile, 51, 51),
    ];

    assert!(lexed.diagnostics.is_empty());
    assert_eq!(lexed.tokens.len(), expected.len());
    for (token, (kind, start, end)) in lexed.tokens.iter().zip(expected) {
        assert_eq!(token.kind, kind);
        assert_range(token, start, end);
    }
}

#[test]
fn recognizes_data_and_pattern_tokens_without_stealing_identifier_boundaries() {
    let source = SourceFile::new(
        "data-pattern-tokens.ash",
        "type newtype match _ Tree Leaf newtype_ _tail | =>",
    )
    .expect("the token source should fit");

    assert_eq!(
        token_kinds(&source),
        vec![
            TokenKind::Type,
            TokenKind::Newtype,
            TokenKind::Match,
            TokenKind::Wildcard,
            TokenKind::UpperIdentifier("Tree".into()),
            TokenKind::UpperIdentifier("Leaf".into()),
            TokenKind::Identifier("newtype_".into()),
            TokenKind::Identifier("_tail".into()),
            TokenKind::Pipe,
            TokenKind::FatArrow,
            TokenKind::EndOfFile,
        ]
    );
}

#[test]
fn recognizes_module_tokens_with_exact_spans_and_reserved_word_boundaries() {
    let source = SourceFile::new(
        "module-tokens.ash",
        "import as pub opaque newtype importable as_ pubx opaque_ newtypex @ .\n",
    )
    .expect("the token source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");
    let expected = [
        (TokenKind::Import, 0, 6),
        (TokenKind::As, 7, 9),
        (TokenKind::Pub, 10, 13),
        (TokenKind::Opaque, 14, 20),
        (TokenKind::Newtype, 21, 28),
        (TokenKind::Identifier("importable".into()), 29, 39),
        (TokenKind::Identifier("as_".into()), 40, 43),
        (TokenKind::Identifier("pubx".into()), 44, 48),
        (TokenKind::Identifier("opaque_".into()), 49, 56),
        (TokenKind::Identifier("newtypex".into()), 57, 65),
        (TokenKind::At, 66, 67),
        (TokenKind::Dot, 68, 69),
        (TokenKind::LineEnd, 69, 70),
        (TokenKind::EndOfFile, 70, 70),
    ];

    assert!(lexed.diagnostics.is_empty());
    assert_eq!(lexed.tokens.len(), expected.len());
    for (token, (kind, start, end)) in lexed.tokens.iter().zip(expected) {
        assert_eq!(token.kind, kind);
        assert_range(token, start, end);
        assert_eq!(token.span.source(), source.id());
    }
}

fn assert_range(token: &Token, start: u32, end: u32) {
    assert_eq!(token.span.range().start(), start);
    assert_eq!(token.span.range().end(), end);
}

#[test]
fn recognizes_the_closed_token_family_and_reserved_word_boundaries() {
    let source = SourceFile::new(
        "tokens.ash",
        "fn let type newtype Int Bool Unit true false name_1 fnn newtype_ 18446744073709551616 ( ) { } : = == + * -> , < > ;",
    )
    .expect("the token source should fit");

    assert_eq!(
        token_kinds(&source),
        vec![
            TokenKind::Fn,
            TokenKind::Let,
            TokenKind::Type,
            TokenKind::Newtype,
            TokenKind::IntType,
            TokenKind::BoolType,
            TokenKind::UnitType,
            TokenKind::True,
            TokenKind::False,
            TokenKind::Identifier("name_1".into()),
            TokenKind::Identifier("fnn".into()),
            TokenKind::Identifier("newtype_".into()),
            TokenKind::Integer(
                ash::integer::Integer::parse_decimal("18446744073709551616")
                    .expect("the test literal should be valid"),
            ),
            TokenKind::LeftParen,
            TokenKind::RightParen,
            TokenKind::LeftBrace,
            TokenKind::RightBrace,
            TokenKind::Colon,
            TokenKind::Equal,
            TokenKind::EqualEqual,
            TokenKind::Plus,
            TokenKind::Star,
            TokenKind::Arrow,
            TokenKind::Comma,
            TokenKind::Less,
            TokenKind::Greater,
            TokenKind::Semicolon,
            TokenKind::EndOfFile,
        ]
    );
}

#[test]
fn every_closed_token_kind_has_an_exact_span_in_one_stream() {
    let source_text =
        "name 0 true false fn let type newtype Int Bool Unit ( ) { } : = == + * -> , < > ;\n";
    let source =
        SourceFile::new("closed-family.ash", source_text).expect("the token source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");
    let expected = [
        (TokenKind::Identifier("name".into()), 0, 4),
        (
            TokenKind::Integer(
                ash::integer::Integer::parse_decimal("0")
                    .expect("zero should be a valid integer literal"),
            ),
            5,
            6,
        ),
        (TokenKind::True, 7, 11),
        (TokenKind::False, 12, 17),
        (TokenKind::Fn, 18, 20),
        (TokenKind::Let, 21, 24),
        (TokenKind::Type, 25, 29),
        (TokenKind::Newtype, 30, 37),
        (TokenKind::IntType, 38, 41),
        (TokenKind::BoolType, 42, 46),
        (TokenKind::UnitType, 47, 51),
        (TokenKind::LeftParen, 52, 53),
        (TokenKind::RightParen, 54, 55),
        (TokenKind::LeftBrace, 56, 57),
        (TokenKind::RightBrace, 58, 59),
        (TokenKind::Colon, 60, 61),
        (TokenKind::Equal, 62, 63),
        (TokenKind::EqualEqual, 64, 66),
        (TokenKind::Plus, 67, 68),
        (TokenKind::Star, 69, 70),
        (TokenKind::Arrow, 71, 73),
        (TokenKind::Comma, 74, 75),
        (TokenKind::Less, 76, 77),
        (TokenKind::Greater, 78, 79),
        (TokenKind::Semicolon, 80, 81),
        (TokenKind::LineEnd, 81, 82),
        (TokenKind::EndOfFile, 82, 82),
    ];

    assert!(lexed.diagnostics.is_empty());
    assert_eq!(lexed.tokens.len(), expected.len());
    for (token, (kind, start, end)) in lexed.tokens.iter().zip(expected) {
        assert_eq!(token.kind, kind);
        assert_range(token, start, end);
        assert_eq!(token.span.source(), source.id());
    }
}

#[test]
fn every_token_carries_an_exact_checked_source_span() {
    let source = SourceFile::new("spans.ash", "fn 9001").expect("the span source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");

    assert!(lexed.diagnostics.is_empty());
    assert_eq!(lexed.tokens.len(), 3);
    assert_range(&lexed.tokens[0], 0, 2);
    assert_range(&lexed.tokens[1], 3, 7);
    assert_range(&lexed.tokens[2], 7, 7);
    assert_eq!(lexed.tokens[0].span.source(), source.id());
}

#[test]
fn emits_exact_lf_and_crlf_boundaries_but_ignores_blank_logical_lines() {
    let source =
        SourceFile::new("lines.ash", "\n\nx\n\ny\r\n\r\n").expect("the line source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");

    assert!(lexed.diagnostics.is_empty());
    assert_eq!(
        lexed
            .tokens
            .iter()
            .map(|token| token.kind.clone())
            .collect::<Vec<_>>(),
        vec![
            TokenKind::Identifier("x".into()),
            TokenKind::LineEnd,
            TokenKind::Identifier("y".into()),
            TokenKind::LineEnd,
            TokenKind::EndOfFile,
        ]
    );
    assert_range(&lexed.tokens[1], 3, 4);
    assert_range(&lexed.tokens[3], 6, 8);
    assert_range(&lexed.tokens[4], 10, 10);
}

#[test]
fn suppresses_parenthesized_newlines() {
    let source = SourceFile::new("group.ash", "(\nx\n)\n").expect("the grouped source should fit");

    assert_eq!(
        token_kinds(&source),
        vec![
            TokenKind::LeftParen,
            TokenKind::Identifier("x".into()),
            TokenKind::RightParen,
            TokenKind::LineEnd,
            TokenKind::EndOfFile,
        ]
    );
}

#[test]
fn a_block_inside_parentheses_reenables_then_restores_line_boundaries() {
    let source =
        SourceFile::new("nested.ash", "(\n{\nx\n}\n)\n").expect("the nested source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");

    assert_eq!(
        lexed
            .tokens
            .iter()
            .map(|token| token.kind.clone())
            .collect::<Vec<_>>(),
        vec![
            TokenKind::LeftParen,
            TokenKind::LeftBrace,
            TokenKind::LineEnd,
            TokenKind::Identifier("x".into()),
            TokenKind::LineEnd,
            TokenKind::RightBrace,
            TokenKind::RightParen,
            TokenKind::LineEnd,
            TokenKind::EndOfFile,
        ]
    );
    assert_range(&lexed.tokens[2], 3, 4);
    assert_range(&lexed.tokens[4], 5, 6);
    assert_range(&lexed.tokens[7], 9, 10);
}

#[test]
fn reports_each_excluded_lexical_form_with_its_exact_span() {
    let cases = [
        ("\r", LexReason::BareCarriageReturn, 1),
        ("\u{feff}", LexReason::ByteOrderMark, 3),
        ("café", LexReason::UnicodeIdentifier, 5),
        ("// no", LexReason::Comment, 5),
        ("/* no */", LexReason::Comment, 8),
        ("-123", LexReason::NegativeLiteral, 4),
        ("01", LexReason::InvalidIntegerLiteral, 2),
        ("$", LexReason::UnknownCharacter, 1),
        ("😀", LexReason::UnknownCharacter, 4),
    ];

    for (text, reason, end) in cases {
        let source =
            SourceFile::new("invalid.ash", text).expect("the invalid test source should still fit");
        let lexed = lex(&source).expect("the source should remain representable while lexing");

        assert_eq!(lexed.diagnostics.len(), 1, "source: {text:?}");
        assert_eq!(lexed.diagnostics[0].reason, reason, "source: {text:?}");
        assert_eq!(
            lexed.diagnostics[0].primary.span().range().start(),
            0,
            "source: {text:?}"
        );
        assert_eq!(
            lexed.diagnostics[0].primary.span().range().end(),
            end,
            "source: {text:?}"
        );
        assert_eq!(
            lexed.tokens.last().map(|token| &token.kind),
            Some(&TokenKind::EndOfFile),
            "source: {text:?}"
        );
    }
}

#[test]
fn lexical_errors_keep_expected_and_found_forms_as_structured_fields() {
    let source = SourceFile::new("negative.ash", "-42").expect("the negative source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");
    let diagnostic = &lexed.diagnostics[0];

    assert_eq!(diagnostic.reason, LexReason::NegativeLiteral);
    assert_eq!(
        diagnostic.expected.as_deref(),
        Some("a nonnegative decimal integer")
    );
    assert_eq!(diagnostic.found.as_deref(), Some("-42"));
}

#[test]
fn collects_independent_lexical_errors_while_always_making_progress() {
    let source = SourceFile::new("errors.ash", "?\r$😀").expect("the error source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");

    assert_eq!(
        lexed
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.reason)
            .collect::<Vec<_>>(),
        vec![
            LexReason::UnknownCharacter,
            LexReason::BareCarriageReturn,
            LexReason::UnknownCharacter,
            LexReason::UnknownCharacter,
        ]
    );
    assert_range(
        lexed
            .tokens
            .last()
            .expect("lexing should always append end of file"),
        7,
        7,
    );
}

#[test]
fn mismatched_closers_are_tokens_and_do_not_corrupt_parenthesized_context() {
    let source =
        SourceFile::new("mismatch.ash", "(\n}\nx\n)\n").expect("the mismatch source should fit");

    assert_eq!(
        token_kinds(&source),
        vec![
            TokenKind::LeftParen,
            TokenKind::RightBrace,
            TokenKind::Identifier("x".into()),
            TokenKind::RightParen,
            TokenKind::LineEnd,
            TokenKind::EndOfFile,
        ]
    );
}

#[test]
fn mismatched_closers_are_tokens_and_do_not_corrupt_block_context() {
    let source =
        SourceFile::new("mismatch.ash", "{\n)\nx\n}\n").expect("the mismatch source should fit");

    assert_eq!(
        token_kinds(&source),
        vec![
            TokenKind::LeftBrace,
            TokenKind::LineEnd,
            TokenKind::RightParen,
            TokenKind::LineEnd,
            TokenKind::Identifier("x".into()),
            TokenKind::LineEnd,
            TokenKind::RightBrace,
            TokenKind::LineEnd,
            TokenKind::EndOfFile,
        ]
    );
}

#[test]
fn unmatched_closers_remain_available_for_parser_diagnostics() {
    let source = SourceFile::new("closers.ash", ") }\n").expect("the closer source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");

    assert!(lexed.diagnostics.is_empty());
    assert_eq!(
        lexed
            .tokens
            .iter()
            .map(|token| token.kind.clone())
            .collect::<Vec<_>>(),
        vec![
            TokenKind::RightParen,
            TokenKind::RightBrace,
            TokenKind::LineEnd,
            TokenKind::EndOfFile,
        ]
    );
    assert_range(&lexed.tokens[0], 0, 1);
    assert_range(&lexed.tokens[1], 2, 3);
}

#[test]
fn rejected_block_comments_cover_unicode_newlines_and_bare_carriage_returns() {
    let cases = [("/* β\n*/", 8), ("/* β\n", 6), ("/*\r*/", 5)];

    for (text, end) in cases {
        let source =
            SourceFile::new("comment.ash", text).expect("the rejected comment source should fit");
        let lexed = lex(&source).expect("the source should remain representable while lexing");

        assert_eq!(lexed.diagnostics.len(), 1, "source: {text:?}");
        let diagnostic = &lexed.diagnostics[0];
        assert_eq!(diagnostic.reason, LexReason::Comment, "source: {text:?}");
        assert_eq!(diagnostic.primary.span().range().start(), 0);
        assert_eq!(diagnostic.primary.span().range().end(), end);
        assert_eq!(
            lexed
                .tokens
                .iter()
                .map(|token| &token.kind)
                .collect::<Vec<_>>(),
            vec![&TokenKind::EndOfFile]
        );
        assert_range(&lexed.tokens[0], end, end);
    }
}

#[test]
fn a_combining_mark_adjacent_to_an_ascii_identifier_is_rejected_at_its_bytes() {
    let source = SourceFile::new("combining.ash", "cafe\u{301}")
        .expect("the combining-mark source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");

    assert_eq!(lexed.diagnostics.len(), 1);
    assert_eq!(lexed.diagnostics[0].reason, LexReason::UnknownCharacter);
    assert_eq!(lexed.diagnostics[0].found.as_deref(), Some("\u{301}"));
    assert_eq!(
        (
            lexed.diagnostics[0].primary.span().range().start(),
            lexed.diagnostics[0].primary.span().range().end(),
        ),
        (4, 6),
    );
    assert_eq!(
        lexed
            .tokens
            .iter()
            .map(|token| &token.kind)
            .collect::<Vec<_>>(),
        vec![&TokenKind::Identifier("cafe".into()), &TokenKind::EndOfFile,]
    );
    assert_range(&lexed.tokens[0], 0, 4);
    assert_range(&lexed.tokens[1], 6, 6);
}

#[test]
fn crlf_boundaries_follow_nested_parenthesis_and_block_contexts() {
    let source = SourceFile::new("nested-crlf.ash", "(\r\n{\r\nx\r\n}\r\n)\r\n")
        .expect("the nested CRLF source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");

    assert!(lexed.diagnostics.is_empty());
    assert_eq!(
        lexed
            .tokens
            .iter()
            .map(|token| &token.kind)
            .collect::<Vec<_>>(),
        vec![
            &TokenKind::LeftParen,
            &TokenKind::LeftBrace,
            &TokenKind::LineEnd,
            &TokenKind::Identifier("x".into()),
            &TokenKind::LineEnd,
            &TokenKind::RightBrace,
            &TokenKind::RightParen,
            &TokenKind::LineEnd,
            &TokenKind::EndOfFile,
        ]
    );
    assert_range(&lexed.tokens[2], 4, 6);
    assert_range(&lexed.tokens[4], 7, 9);
    assert_range(&lexed.tokens[7], 13, 15);
    assert_range(&lexed.tokens[8], 15, 15);
}

#[test]
fn eof_directly_after_a_token_uses_the_source_end() {
    let source = SourceFile::new("eof.ash", "value").expect("the EOF source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");

    assert_eq!(
        token_kinds(&source),
        vec![TokenKind::Identifier("value".into()), TokenKind::EndOfFile,]
    );
    assert_range(&lexed.tokens[0], 0, 5);
    assert_range(&lexed.tokens[1], 5, 5);
}

#[test]
fn lone_minus_and_slash_are_independent_unknown_characters() {
    let source =
        SourceFile::new("unknown.ash", "- /").expect("the unknown-character source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");

    assert_eq!(
        lexed
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.reason)
            .collect::<Vec<_>>(),
        vec![LexReason::UnknownCharacter, LexReason::UnknownCharacter]
    );
    assert_eq!(lexed.diagnostics[0].found.as_deref(), Some("-"));
    assert_eq!(lexed.diagnostics[1].found.as_deref(), Some("/"));
    assert_eq!(lexed.diagnostics[0].primary.span().range().start(), 0);
    assert_eq!(lexed.diagnostics[0].primary.span().range().end(), 1);
    assert_eq!(lexed.diagnostics[1].primary.span().range().start(), 2);
    assert_eq!(lexed.diagnostics[1].primary.span().range().end(), 3);
    assert_eq!(lexed.tokens.len(), 1);
    assert_range(&lexed.tokens[0], 3, 3);
}

#[test]
fn adjacent_integer_and_identifier_tokens_split_at_the_normative_boundaries() {
    let source =
        SourceFile::new("adjacent.ash", "1_2").expect("the adjacent-token source should fit");
    let lexed = lex(&source).expect("the source should remain representable while lexing");

    assert_eq!(
        token_kinds(&source),
        vec![
            TokenKind::Integer(
                ash::integer::Integer::parse_decimal("1")
                    .expect("one should be a valid integer literal"),
            ),
            TokenKind::Identifier("_2".into()),
            TokenKind::EndOfFile,
        ]
    );
    assert_range(&lexed.tokens[0], 0, 1);
    assert_range(&lexed.tokens[1], 1, 3);
    assert_range(&lexed.tokens[2], 3, 3);
}

#[test]
fn syntax_work_budget_stops_token_retention_before_the_next_allocation() {
    let source = SourceFile::new("token-work-limit.ash", ",".repeat(SYNTAX_WORK_LIMIT + 1))
        .expect("the token work fixture should fit");

    let lexed = lex(&source).expect("resource exhaustion preserves source invariants");

    assert_eq!(
        lexed.resource_failure(),
        Some(ResourceFailure::SyntaxWork {
            limit: SYNTAX_WORK_LIMIT
        })
    );
    assert_eq!(lexed.tokens.len(), SYNTAX_WORK_LIMIT);
    assert!(lexed.diagnostics.is_empty());
    assert!(!matches!(
        lexed.tokens.last().map(|token| &token.kind),
        Some(TokenKind::EndOfFile)
    ));
}
