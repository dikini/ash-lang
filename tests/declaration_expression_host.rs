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
fn imported_expression_capture_roundtrips_through_the_checked_host() {
    run("tests/fixtures/surface-macros/expression-host/main.ash");
}

#[test]
fn imported_mixed_captures_bind_the_returned_expression() {
    run("tests/fixtures/surface-macros/expression-host/mixed_main.ash");
}
