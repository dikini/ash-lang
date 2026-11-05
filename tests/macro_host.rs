use std::path::PathBuf;

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    lexer::lex,
    module::ModuleRoots,
    parser::{parse, project_module},
    source::SourceFile,
};

#[test]
fn frozen_transformer_body_parses_as_ordinary_ash() {
    let fixture = include_str!("fixtures/surface-macros/macros.ash");
    let start = fixture
        .find("expand_twice :")
        .expect("transformer signature");
    let source = SourceFile::new("transformer.ash", fixture[start..].to_owned()).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(tree.lexical_diagnostics().is_empty(), "{tree:?}");
    assert!(tree.parse_diagnostics().is_empty(), "{tree:?}");
    project_module(&source, &tree).expect("ordinary transformer projects");
}

#[test]
fn checked_ash_transformer_constructs_expression_from_capture() {
    let configuration = RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/surface-macros/entry_host.ash"),
        roots: ModuleRoots::empty(),
    };
    let compiled = compile_path(configuration).expect("macro host graph compiles");
    let actual = execute(&compiled).expect("macro host graph executes");
    assert_eq!(actual.value_display(), "42");
    assert_eq!(actual.type_display(), "Int");
}
