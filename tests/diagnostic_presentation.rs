use ash::{
    lexer::{LexReason, lex},
    message::{Catalogue, Locale},
    presentation::{compile_lex_diagnostic, write_json, write_short},
    source::SourceFile,
};

#[test]
fn lexical_messages_localize_restrictions_but_preserve_source_facts() {
    let cases = [
        (
            "\r",
            LexReason::BareCarriageReturn,
            "A carriage return must be followed by a line feed (CRLF); a line feed (LF) also starts a new line.",
            "След символ за връщане на каретката трябва да има символ за нов ред (CRLF); самостоятелен символ за нов ред (LF) също е допустим.",
        ),
        (
            "\u{feff}",
            LexReason::ByteOrderMark,
            "Ash source files must not contain a byte order mark (BOM).",
            "Изходните файлове на Ash не трябва да съдържат маркер за реда на байтовете (BOM).",
        ),
        (
            "имя",
            LexReason::UnicodeIdentifier,
            "Ash identifiers use only ASCII letters, digits and underscores.",
            "Имената в Ash използват само ASCII букви, цифри и долни черти.",
        ),
        (
            "// note",
            LexReason::Comment,
            "Ash does not support comments.",
            "Ash не поддържа коментари.",
        ),
        (
            "-1",
            LexReason::NegativeLiteral,
            "Ash does not support negative integer literals.",
            "Ash не поддържа отрицателни целочислени литерали.",
        ),
        (
            "01",
            LexReason::InvalidIntegerLiteral,
            "An integer literal must be 0 or a sequence of ASCII digits without a leading zero.",
            "Целочисленият литерал трябва да е 0 или поредица от ASCII цифри без водеща нула.",
        ),
        (
            "?",
            LexReason::UnknownCharacter,
            "This character cannot begin an Ash token.",
            "Този символ не може да започва лексикална единица в Ash.",
        ),
    ];
    for (text, reason, english, bulgarian) in cases {
        let source = SourceFile::new("lexical.ash", text).unwrap();
        let mut lexed = lex(&source).unwrap();
        assert_eq!(lexed.diagnostics.len(), 1);
        let diagnostic = &mut lexed.diagnostics[0];
        assert_eq!(diagnostic.reason, reason);
        // Legacy prose is not an input to localized messages or JSON facts.
        diagnostic.expected = Some("unrelated legacy explanation".into());
        let view = compile_lex_diagnostic(diagnostic, &[&source]).unwrap();
        for (locale, expected) in [(Locale::English, english), (Locale::Bulgarian, bulgarian)] {
            let mut output = Vec::new();
            write_short(&mut output, &view, &Catalogue::new(locale).unwrap()).unwrap();
            assert_eq!(
                String::from_utf8(output).unwrap(),
                format!("lexical.ash:1:1: {expected} [{reason}]\n")
            );
        }
        let mut output = Vec::new();
        write_json(&mut output, &view).unwrap();
        assert_eq!(output.iter().filter(|&&b| b == b'\n').count(), 1);
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["reason"], reason.to_string());
        assert_eq!(
            json["facts"],
            serde_json::json!([{"name":"found", "kind":"code", "value":text}])
        );
        assert_eq!(json["labels"][0]["relationship"], "invalid_token");
        assert_eq!(json["labels"][0]["byte_start"], 0);
        assert_eq!(json["labels"][0]["byte_end"], text.len());
    }
}

#[test]
fn parser_retains_expected_form_found_category_and_recovery_position() {
    use ash::parser::{ExpectedForm, FoundToken, ParseReason, parse};
    let text = "main : Unit -> Int\nmain () = (41\n";
    let source = SourceFile::new("group.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    let [diagnostic] = tree.parse_diagnostics() else {
        panic!("one unclosed group");
    };
    assert_eq!(diagnostic.reason, ParseReason::UnclosedGroup);
    assert_eq!(diagnostic.expected_form(), Some(ExpectedForm::RightParen));
    assert_eq!(diagnostic.found_token(), Some(FoundToken::EndOfFile));
    assert_eq!(
        diagnostic.recovery_position().unwrap().range().start() as usize,
        text.len()
    );
    assert!(diagnostic.context.is_empty());
}

#[test]
fn parser_keeps_fixed_tokens_distinct_from_description_categories() {
    use ash::parser::{FoundToken, ParseReason, parse};
    let source = SourceFile::new("semicolon.ash", "main : Unit -> Int\nmain () = 1;\n").unwrap();
    let tree = parse(lex(&source).unwrap());
    let diagnostic = tree
        .parse_diagnostics()
        .iter()
        .find(|d| d.reason == ParseReason::Semicolon)
        .unwrap();
    assert_eq!(diagnostic.found_token(), Some(FoundToken::Spelling(";")));
    assert_eq!(diagnostic.expected_form(), None);
    assert_eq!(diagnostic.recovery_position(), None);
}
