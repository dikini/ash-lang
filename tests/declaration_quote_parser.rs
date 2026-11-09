use ash::{lexer::lex, parser::parse, source::SourceFile};

#[test]
fn inline_escape_within_expression_quote_parses() {
    let source = SourceFile::new(
        "inline-escape.ash",
        "probe : Unit -> Int\nprobe () = syntax { ${ 42 } }\n",
    )
    .unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(tree.parse_diagnostics().is_empty(), "{:?}", tree.parse_diagnostics());
}
