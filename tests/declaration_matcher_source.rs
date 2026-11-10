use std::path::PathBuf;

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
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
