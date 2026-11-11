use std::path::PathBuf;

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};

#[test]
fn fixed_derive_main_executes_through_public_pipeline() {
    let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("docs/design/macros/fixtures/derives/main.ash");
    let program = compile_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect("both derives apply to each original nominal declaration");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn fixed_indexed_derives_execute_for_one_two_and_three_constructors() {
    for name in ["one.ash", "main.ash", "three.ash"] {
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/indexed")
            .join(name);
        let program = compile_path(RunConfiguration {
            entry,
            roots: ModuleRoots::empty(),
        })
        .unwrap_or_else(|error| panic!("{name}: {error:?}"));
        assert_eq!(execute(&program).unwrap().value_display(), "42", "{name}");
    }
}
