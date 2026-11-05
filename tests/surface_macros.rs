use std::path::PathBuf;

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};

fn fixture(name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/surface-macros")
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

#[test]
fn handwritten_graph_observes_the_frozen_value() {
    let compiled = compile_path(fixture("handwritten.ash")).expect("handwritten graph compiles");
    let result = execute(&compiled).expect("handwritten graph executes");
    assert_eq!(result.value_display(), "42");
}

#[test]
fn imported_templates_and_ash_transformer_run_through_the_driver() {
    let handwritten = compile_path(fixture("handwritten.ash")).expect("handwritten graph compiles");
    let expected = execute(&handwritten).expect("handwritten graph executes");
    let expanded = compile_path(fixture("entry.ash")).expect("macro graph compiles");
    let actual = execute(&expanded).expect("macro graph executes");
    assert_eq!(actual.value_display(), expected.value_display());
    assert_eq!(actual.value_display(), "42");
    assert_eq!(actual.type_display(), expected.type_display());
}

#[test]
fn template_macro_preserves_expression_capture_grouping() {
    let compiled = compile_path(fixture("template-only/entry.ash"))
        .expect("the imported template graph compiles");
    let actual = execute(&compiled).expect("the template graph executes");
    assert_eq!(actual.value_display(), "35");
    assert_eq!(actual.type_display(), "Int");
}

#[test]
fn renamed_template_macro_uses_the_selected_export() {
    let compiled = compile_path(fixture("template-only/renamed.ash"))
        .expect("the renamed syntax graph compiles");
    assert_eq!(execute(&compiled).unwrap().value_display(), "35");
}

#[test]
fn selected_template_without_capture_is_a_syntax_error() {
    let failure = compile_path(fixture("template-only/malformed.ash")).unwrap_err();
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert!(matches!(
        failure.graph_failure(),
        Some(ash::module::LoadGraphError::Syntax(_))
    ));
}

#[test]
fn template_graph_preserves_bindings_and_private_helpers() {
    let compiled =
        compile_path(fixture("template-graph/entry.ash")).expect("the template graph compiles");
    let actual = execute(&compiled).expect("the template graph executes");
    assert_eq!(actual.value_display(), "42");
    assert_eq!(actual.type_display(), "Int");
}
