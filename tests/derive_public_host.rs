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
fn derive_without_optional_name_reports_missing_second_capture() {
    let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/surface-macros/derive-host-subject/main.ash");
    let program = compile_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect("the host receives the declaration and no second capture");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
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

#[test]
fn fixed_derive_failures_retain_subject_and_nested_expansion_origins() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    fn label_matches(
        labels: &[serde_json::Value],
        relationship: &str,
        suffix: &str,
        expected: &str,
    ) -> bool {
        labels.iter().any(|label| {
            let Some(path) = label["path"].as_str() else {
                return false;
            };
            if label["relationship"] != relationship || !path.ends_with(suffix) {
                return false;
            }
            let text = std::fs::read_to_string(path).unwrap();
            let start = label["byte_start"].as_u64().unwrap() as usize;
            let end = label["byte_end"].as_u64().unwrap() as usize;
            &text[start..end] == expected
        })
    }

    for (entry, message, subject_file, subject) in [
        (
            "ordered_first.ash",
            "first derive rejected",
            "ordered_first.ash",
            "Color",
        ),
        (
            "ordered_second.ash",
            "second derive rejected",
            "ordered_second.ash",
            "Color",
        ),
        (
            "generated_order.ash",
            "second derive rejected",
            "generated_order.ash",
            "Source",
        ),
        (
            "generated_failure.ash",
            "first derive rejected",
            "generated_failure_forms.ash",
            "Generated",
        ),
    ] {
        let failure = compile_path(RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("docs/design/macros/fixtures/derives")
                .join(entry),
            roots: ModuleRoots::empty(),
        })
        .expect_err("the selected derive rejects");
        let Some(PipelineFailure::SyntaxExpansion(rejection)) = failure.pipeline_failure() else {
            panic!("{entry}: expected an authored rejection: {failure:?}");
        };
        assert_eq!(rejection.message(), message);
        assert!(rejection.teardown().is_none());
        let diagnostics = compile_file_diagnostics(&failure).unwrap();
        let [diagnostic] = diagnostics.as_slice() else {
            panic!("{entry}: exactly one diagnostic");
        };
        let mut output = Vec::new();
        write_json(&mut output, diagnostic).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["reason"], "syntax.rejected");
        let labels = json["labels"].as_array().unwrap();
        assert!(
            label_matches(labels, "syntax_cause", subject_file, subject),
            "{entry}: {json}"
        );
        assert!(
            labels
                .iter()
                .any(|label| label["relationship"] == "syntax_definition"
                    && label["path"]
                        .as_str()
                        .unwrap()
                        .ends_with("ordering_forms.ash")),
            "{entry}: {json}"
        );
        if entry == "generated_failure.ash" {
            assert!(
                label_matches(
                    labels,
                    "syntax_cause",
                    "generated_failure_forms.ash",
                    "first_failure"
                ),
                "{json}"
            );
            assert!(
                label_matches(labels, "syntax_invocation", entry, "spawn_failure"),
                "{json}"
            );
            assert!(
                labels
                    .iter()
                    .any(|label| label["relationship"] == "syntax_definition"
                        && label["path"]
                            .as_str()
                            .unwrap()
                            .ends_with("generated_failure_forms.ash")),
                "{json}"
            );
        }
    }
}
