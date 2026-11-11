use std::path::PathBuf;

use ash::{
    driver::{PipelineFailure, RunConfiguration, compile_path, execute},
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

#[test]
fn fixed_mixed_expansions_report_the_first_authored_rejection() {
    for (name, message) in [
        ("derive_first.ash", "derive rejected"),
        ("declaration_first.ash", "declaration rejected"),
    ] {
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/diagnostics")
            .join(name);
        let failure = compile_path(RunConfiguration {
            entry,
            roots: ModuleRoots::empty(),
        })
        .expect_err("the first authored transformer rejects");
        let Some(PipelineFailure::SyntaxExpansion(rejection)) = failure.pipeline_failure() else {
            panic!("{name}: expected the authored rejection, got {failure:?}");
        };
        assert_eq!(rejection.message(), message, "{name}");
        assert!(rejection.teardown().is_none(), "{name}");
    }
}

#[test]
fn checked_import_output_is_refused_before_a_later_derive_runs() {
    for name in ["single.ash", "ordered.ash"] {
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/surface-macros/derive-import")
            .join(name);
        let failure = compile_path(RunConfiguration {
            entry,
            roots: ModuleRoots::empty(),
        })
        .expect_err("a checked transformer cannot publish an import");
        assert!(failure.is_source_rejection(), "{name}: {failure:?}");
        assert!(
            failure.reason_code().starts_with("parse."),
            "{name}: {failure:?}"
        );
    }
}

#[test]
fn fixed_derive_lists_preserve_authored_and_nested_failure_order() {
    for (name, message) in [
        ("ordered_first.ash", "first derive rejected"),
        ("ordered_second.ash", "second derive rejected"),
        ("generated_failure.ash", "first derive rejected"),
        ("generated_order.ash", "second derive rejected"),
    ] {
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/derives")
            .join(name);
        let failure = compile_path(RunConfiguration {
            entry,
            roots: ModuleRoots::empty(),
        })
        .expect_err("the selected derive rejects");
        let Some(PipelineFailure::SyntaxExpansion(rejection)) = failure.pipeline_failure() else {
            panic!("{name}: expected an authored rejection, got {failure:?}");
        };
        assert_eq!(rejection.message(), message, "{name}");
        assert!(rejection.teardown().is_none(), "{name}");
    }
}
