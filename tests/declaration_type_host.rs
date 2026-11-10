use std::path::PathBuf;

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    message::{Catalogue, Locale},
    module::ModuleRoots,
    presentation::{compile_file_diagnostics, write_human, write_json},
};

fn fixture(path: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path),
        roots: ModuleRoots::empty(),
    }
}

#[test]
fn imported_type_capture_roundtrips_into_the_caller_function() {
    for path in [
        "tests/fixtures/surface-macros/type-host/control.ash",
        "tests/fixtures/surface-macros/type-host/main.ash",
    ] {
        let program =
            compile_path(fixture(path)).unwrap_or_else(|failure| panic!("{path}: {failure:?}"));
        let value = execute(&program).expect("the checked function executes");
        assert_eq!(value.value_display(), "42", "{path}");
        assert_eq!(value.type_display(), "Int", "{path}");
    }
}

#[test]
fn fixed_i14_type_node_is_rejected_as_a_declaration() {
    let failure = compile_path(fixture(
        "docs/design/macros/fixtures/diagnostics/category.ash",
    ))
    .expect_err("a whole TypeNode cannot be a declaration");
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert_eq!(
        failure.reason_code(),
        "parse.unexpected-token",
        "{failure:?}"
    );

    let diagnostics = compile_file_diagnostics(&failure).expect("category failure is presentable");
    let [diagnostic] = diagnostics.as_slice() else {
        panic!("expected one category diagnostic: {diagnostics:?}");
    };
    let mut human = Vec::new();
    write_human(
        &mut human,
        diagnostic,
        &Catalogue::new(Locale::English).unwrap(),
    )
    .unwrap();
    let human = String::from_utf8(human).unwrap();
    assert!(human.contains("category.ash"), "{human}");
    assert!(human.contains("category_forms.ash"), "{human}");

    let mut json = Vec::new();
    write_json(&mut json, diagnostic).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    assert_eq!(json["reason"], "parse.unexpected-token", "{json}");
    let labels = json["labels"].as_array().expect("source labels");
    assert!(
        labels.iter().any(|label| {
            label["relationship"] == "syntax_invocation"
                && label["path"]
                    .as_str()
                    .is_some_and(|path| path.ends_with("category.ash"))
        }),
        "{json}"
    );
    assert!(
        labels.iter().any(|label| {
            label["relationship"] == "syntax_definition"
                && label["path"]
                    .as_str()
                    .is_some_and(|path| path.ends_with("category_forms.ash"))
        }),
        "{json}"
    );
}
