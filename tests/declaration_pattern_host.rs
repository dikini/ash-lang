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
    let value = execute(&program).expect("the generated identity executes");
    assert_eq!(value.value_display(), "42");
    assert_eq!(value.type_display(), "Int");
}

#[test]
fn imported_pattern_capture_binds_the_caller_reference() {
    run("tests/fixtures/surface-macros/pattern-host/main.ash");
}

#[test]
fn imported_mixed_type_and_pattern_captures_bind_the_caller_reference() {
    run("tests/fixtures/surface-macros/pattern-host/mixed_main.ash");
}

#[test]
fn imported_pattern_and_type_parsers_reject_wrong_categories_and_trailing_nodes() {
    run("tests/fixtures/surface-macros/pattern-host/rejection_main.ash");
}
