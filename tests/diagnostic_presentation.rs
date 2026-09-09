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
fn parser_categories_are_checked_arguments_not_untranslated_english() {
    use ash::{
        message::Message,
        parser::{ExpectedForm, FoundToken},
    };
    let english = Catalogue::new(Locale::English).unwrap();
    let bulgarian = Catalogue::new(Locale::Bulgarian).unwrap();
    let expected = Message::parse_expected(ExpectedForm::Expression);
    assert_eq!(
        english.format(&expected).unwrap(),
        "An expression is required here."
    );
    assert_eq!(bulgarian.format(&expected).unwrap(), "Тук се очаква израз.");
    let found = Message::parse_found(FoundToken::EndOfFile);
    assert_eq!(english.format(&found).unwrap(), "The input ends here.");
    assert_eq!(bulgarian.format(&found).unwrap(), "Входът свършва тук.");
    let punctuation = Message::parse_found(FoundToken::Spelling("=>"));
    assert_eq!(english.format(&punctuation).unwrap(), "Found `=>` here.");
    assert_eq!(bulgarian.format(&punctuation).unwrap(), "Тук има `=>`.");
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
#[test]
fn every_expected_form_has_an_exact_translation() {
    use ash::{message::Message, parser::ExpectedForm};
    let english = Catalogue::new(Locale::English).unwrap();
    let bulgarian = Catalogue::new(Locale::Bulgarian).unwrap();
    let cases = [
        (
            ExpectedForm::Expression,
            "An expression is required here.",
            "Тук се очаква израз.",
        ),
        (
            ExpectedForm::Operand,
            "An operand is required here.",
            "Тук се очаква операнд.",
        ),
        (
            ExpectedForm::Identifier,
            "An identifier is required here.",
            "Тук се очаква име.",
        ),
        (
            ExpectedForm::Type,
            "A type is required here.",
            "Тук се очаква тип.",
        ),
        (
            ExpectedForm::EffectRow,
            "An effect row is required here.",
            "Тук се очаква ред от ефекти.",
        ),
        (
            ExpectedForm::Kind,
            "A kind is required here.",
            "Тук се очаква вид.",
        ),
        (
            ExpectedForm::Pattern,
            "A pattern is required here.",
            "Тук се очаква образец.",
        ),
        (
            ExpectedForm::InterfaceParameter,
            "An interface type parameter is required here.",
            "Тук се очаква типов параметър на интерфейса.",
        ),
        (
            ExpectedForm::InterfaceMethod,
            "An interface method signature is required here.",
            "Тук се очаква сигнатура на метод на интерфейса.",
        ),
        (
            ExpectedForm::EffectOperation,
            "An effect operation signature is required here.",
            "Тук се очаква сигнатура на операция на ефекта.",
        ),
        (
            ExpectedForm::InterfaceApplication,
            "An interface application is required here.",
            "Тук се очаква прилагане на интерфейс.",
        ),
        (
            ExpectedForm::ImplementationMethod,
            "An implementation method equation is required here.",
            "Тук се очаква уравнение за метод на реализацията.",
        ),
        (
            ExpectedForm::Comma,
            "`,` is required here.",
            "Тук се очаква `,`.",
        ),
        (
            ExpectedForm::LeftParen,
            "`(` is required here.",
            "Тук се очаква `(`.",
        ),
        (
            ExpectedForm::RightParen,
            "`)` is required here.",
            "Тук се очаква `)`.",
        ),
        (
            ExpectedForm::LeftBrace,
            "`{` is required here.",
            "Тук се очаква `{`.",
        ),
        (
            ExpectedForm::RightBrace,
            "`}` is required here.",
            "Тук се очаква `}`.",
        ),
        (
            ExpectedForm::Greater,
            "`>` is required here.",
            "Тук се очаква `>`.",
        ),
        (
            ExpectedForm::Colon,
            "`:` is required here.",
            "Тук се очаква `:`.",
        ),
        (
            ExpectedForm::Equal,
            "`=` is required here.",
            "Тук се очаква `=`.",
        ),
        (
            ExpectedForm::Arrow,
            "`->` is required here.",
            "Тук се очаква `->`.",
        ),
        (
            ExpectedForm::FatArrow,
            "`=>` is required here.",
            "Тук се очаква `=>`.",
        ),
        (
            ExpectedForm::LineEnd,
            "A logical line end is required here.",
            "Тук се очаква край на логически ред.",
        ),
        (
            ExpectedForm::EndOfFile,
            "The input must end here.",
            "Входът трябва да свършва тук.",
        ),
    ];
    for (form, en, bg) in cases {
        let message = Message::parse_expected(form);
        assert_eq!(english.format(&message).unwrap(), en, "{form:?}");
        assert_eq!(bulgarian.format(&message).unwrap(), bg, "{form:?}");
    }
}

#[test]
fn every_found_token_category_has_an_exact_translation() {
    use ash::{message::Message, parser::FoundToken};
    let english = Catalogue::new(Locale::English).unwrap();
    let bulgarian = Catalogue::new(Locale::Bulgarian).unwrap();
    for (token, en, bg) in [
        (
            FoundToken::Identifier,
            "An identifier occurs here.",
            "Тук има име.",
        ),
        (
            FoundToken::UpperIdentifier,
            "An uppercase identifier occurs here.",
            "Тук има име с начална главна буква.",
        ),
        (
            FoundToken::Integer,
            "An integer literal occurs here.",
            "Тук има целочислен литерал.",
        ),
        (
            FoundToken::LineEnd,
            "A logical line ends here.",
            "Тук свършва логически ред.",
        ),
        (
            FoundToken::EndOfFile,
            "The input ends here.",
            "Входът свършва тук.",
        ),
        (FoundToken::Spelling("{"), "Found `{` here.", "Тук има `{`."),
    ] {
        let message = Message::parse_found(token);
        assert_eq!(english.format(&message).unwrap(), en);
        assert_eq!(bulgarian.format(&message).unwrap(), bg);
    }
}
#[test]
fn unclosed_group_renders_from_parser_facts_in_both_languages() {
    use ash::{
        parser::parse,
        presentation::{compile_parse_diagnostic, write_human},
    };
    let source = SourceFile::new("group.ash", "main : Unit -> Int\nmain () = (41\n").unwrap();
    let tree = parse(lex(&source).unwrap());
    let view = compile_parse_diagnostic(&tree.parse_diagnostics()[0], &[&source]).unwrap();
    for (locale, title, eof) in [
        (
            Locale::English,
            "This opening parenthesis has no matching `)`.",
            "The input ends here.",
        ),
        (
            Locale::Bulgarian,
            "Тази отваряща скоба няма съответстваща `)`.",
            "Входът свършва тук.",
        ),
    ] {
        let mut output = Vec::new();
        write_human(&mut output, &view, &Catalogue::new(locale).unwrap()).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.starts_with(title));
        assert!(output.contains(eof));
    }
    let mut output = Vec::new();
    write_json(&mut output, &view).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(json["reason"], "parse.unclosed-group");
    assert_eq!(
        json["facts"],
        serde_json::json!([
            {"name":"expected", "kind":"syntax", "value":"right-paren"},
            {"name":"found", "kind":"syntax", "value":"end-of-file"}
        ])
    );
    assert_eq!(json["labels"][0]["relationship"], "opening_group");
    assert_eq!(json["labels"][1]["relationship"], "recovery_position");
    assert_eq!(json["labels"][0]["facts"], serde_json::json!([]));
}
#[test]
fn missing_first_recursive_member_does_not_claim_an_and_delimiter() {
    use ash::{
        parser::{ParseReason, parse},
        presentation::compile_parse_diagnostic,
    };
    let source = SourceFile::new(
        "recursive.ash",
        "main : Unit -> Int\nmain () = {\n    let rec\n    0\n}\n",
    )
    .unwrap();
    let tree = parse(lex(&source).unwrap());
    let diagnostic = tree
        .parse_diagnostics()
        .iter()
        .find(|d| d.reason == ParseReason::ExpectedRecursiveMember)
        .unwrap();
    let view = compile_parse_diagnostic(diagnostic, &[&source]).unwrap();
    let mut output = Vec::new();
    write_short(
        &mut output,
        &view,
        &Catalogue::new(Locale::English).unwrap(),
    )
    .unwrap();
    assert!(
        String::from_utf8(output)
            .unwrap()
            .contains("A recursive binding member is required here.")
    );
    let mut output = Vec::new();
    write_json(&mut output, &view).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(
        json["labels"][0]["relationship"],
        "expected_recursive_member"
    );
}
#[test]
fn parser_json_preserves_order_and_distinct_recovery_causes() {
    use ash::{parser::parse, presentation::compile_parse_diagnostic};
    let source = SourceFile::new(
        "recovery.ash",
        "fn increment(value : Int) -> Int {\n    value +\n}\n\nmain : Unit -> Int\nmain () = (41\n",
    )
    .unwrap();
    let tree = parse(lex(&source).unwrap());
    let mut output = Vec::new();
    for diagnostic in tree.parse_diagnostics() {
        let view = compile_parse_diagnostic(diagnostic, &[&source]).unwrap();
        write_json(&mut output, &view).unwrap();
    }
    let text = String::from_utf8(output).unwrap();
    let lines: Vec<serde_json::Value> = text
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(lines.len(), 2);
    assert_eq!(lines[0]["reason"], "parse.expected-operand");
    assert_eq!(lines[1]["reason"], "parse.unclosed-group");
    assert_eq!(lines[0]["labels"][1]["relationship"], "synchronization");
    assert_eq!(
        lines[0]["labels"][1]["facts"],
        serde_json::json!([
            {"name":"boundary", "kind":"syntax", "value":"block-closing-brace"}
        ])
    );
    assert_eq!(lines[1]["labels"][1]["relationship"], "recovery_position");
}
