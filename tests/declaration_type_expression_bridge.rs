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

fn reject(path: &str) {
    let configuration = RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path),
        roots: ModuleRoots::empty(),
    };
    let failure = compile_path(configuration).expect_err("the protected bridge stays guarded");
    assert_eq!(
        failure.reason_code(),
        "internal.projection.malformed-tree",
        "{failure:?}"
    );
}

#[test]
fn imported_template_keeps_the_captured_type_and_definition_context() {
    run("tests/fixtures/surface-macros/type-expression-bridge/keep_main.ash");
}

#[test]
fn imported_template_copies_the_captured_type_for_each_splice() {
    run("tests/fixtures/surface-macros/type-expression-bridge/twice_main.ash");
}

#[test]
fn protected_type_cannot_reach_an_expression_transformer() {
    reject("tests/fixtures/surface-macros/type-expression-bridge/blocked_main.ash");
}

#[test]
fn protected_type_cannot_cross_a_nested_expression_invocation() {
    reject("tests/fixtures/surface-macros/type-expression-bridge/nested_main.ash");
    reject("tests/fixtures/surface-macros/type-expression-bridge/outer_blocked_main.ash");
}
