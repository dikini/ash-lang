use std::path::PathBuf;

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};

fn run(path: &str) {
    let configuration = RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path),
        roots: ModuleRoots::empty(),
    };
    let program =
        compile_path(configuration).unwrap_or_else(|failure| panic!("{path}: {failure:?}"));
    let value = execute(&program).expect("the generated function executes");
    assert_eq!(value.value_display(), "42");
    assert_eq!(value.type_display(), "Int");
}

#[test]
fn imported_template_keeps_the_captured_type_and_definition_context() {
    run("tests/fixtures/surface-macros/type-expression-bridge/keep_main.ash");
}

#[test]
fn imported_template_copies_the_captured_type_for_each_splice() {
    run("tests/fixtures/surface-macros/type-expression-bridge/twice_main.ash");
}
