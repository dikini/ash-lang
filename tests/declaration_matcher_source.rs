use std::path::PathBuf;

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    lexer::lex,
    module::ModuleRoots,
    parser::{ParseReason, parse},
    source::SourceFile,
};

#[test]
fn imported_grouped_repetitions_accept_an_empty_template() {
    let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/surface-macros/g1-source-ident/main.ash");
    let program = compile_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect("the imported grouped matcher accepts ordered, ragged source identifiers");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn rejects_the_fixed_repetition_separator_follow_ambiguity() {
    let text = include_str!("../docs/design/macros/fixtures/captures/ambiguous_forms.ash");
    let source = SourceFile::new("ambiguous_forms.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(tree.lexical_diagnostics().is_empty());
    assert_eq!(tree.resource_failure(), None);
    let following_separator = text.rfind(", tail").unwrap();
    assert!(
        tree.parse_diagnostics().iter().any(|diagnostic| {
            diagnostic.reason == ParseReason::ExpectedForm
                && diagnostic.primary.span().range().start() as usize == following_separator
        }),
        "{:?}",
        tree.parse_diagnostics()
    );
}
