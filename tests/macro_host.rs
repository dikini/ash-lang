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

#[test]
fn compiler_syntax_module_loads_through_the_driver() {
    let configuration = RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/surface-macros/compiler-syntax-import.ash"),
        roots: ModuleRoots::empty(),
    };
    let compiled = compile_path(configuration).expect("compiler syntax module loads and checks");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

fn macro_fixture(name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/surface-macros")
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

#[test]
fn template_can_invoke_an_imported_transformer_from_another_source() {
    let compiled = compile_path(macro_fixture("entry_procedural_wrapper.ash"))
        .expect("template-invoked transformer compiles");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn unused_transformer_rejects_a_missing_local_target() {
    let failure = compile_path(macro_fixture("invalid_transformer_missing.ash")).unwrap_err();
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert_eq!(failure.reason_code(), "syntax.invalid-transformer");
}

#[test]
fn unused_transformer_rejects_a_wrong_type() {
    let failure = compile_path(macro_fixture("invalid_transformer_type.ash")).unwrap_err();
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert_eq!(failure.reason_code(), "syntax.invalid-transformer");
}

#[test]
fn unused_private_transformer_is_checked_without_being_run() {
    let compiled = compile_path(macro_fixture("unused_private_transformer.ash"))
        .expect("an unused valid private transformer is admitted without running it");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn unused_transformer_rejects_other_effects() {
    let failure = compile_path(macro_fixture("invalid_transformer_effect.ash")).unwrap_err();
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert_eq!(failure.reason_code(), "syntax.invalid-transformer");
}
