use std::path::PathBuf;

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};

fn captures_fixture(name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/captures")
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

#[test]
fn i19_handwritten_binder_control_reaches_the_ordinary_driver() {
    let program = compile_path(captures_fixture("control_binder.ash"))
        .expect("the unchanged handwritten binder control compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn i19_imported_pattern_binder_and_expression_keep_the_caller_context() {
    let program = compile_path(captures_fixture("binder.ash"))
        .expect("the unchanged imported binder graph compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}
