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
