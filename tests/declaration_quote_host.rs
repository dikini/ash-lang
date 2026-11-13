use std::path::PathBuf;

use ash::{
    driver::{PipelineFailure, RunConfiguration, compile_path, execute},
    elaborate::{TypeError, TypeReason},
    eval::RuntimeFailure,
    module::ModuleRoots,
    resolve::ResolveReason,
};

fn configuration(path: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path),
        roots: ModuleRoots::empty(),
    }
}

fn result(path: &str, expected: &str) {
    let program =
        compile_path(configuration(path)).unwrap_or_else(|failure| panic!("{path}: {failure:?}"));
    let value = execute(&program).expect("the checked program executes");
    assert_eq!(value.value_display(), expected);
    assert_eq!(value.type_display(), "Int");
}

#[test]
fn fixed_i17_helper_slice_crosses_a_real_dependency() {
    let original = include_str!("../docs/design/macros/fixtures/generators/forms.ash");
    let helpers = include_str!("fixtures/surface-macros/quote-i17-dependency/helpers.ash");
    let prefix = original
        .split_once("wrong_syntax :")
        .expect("the fixed helper boundary remains present")
        .0;
    assert!(helpers.starts_with(prefix));
    result(
        "tests/fixtures/surface-macros/quote-i17-dependency/entry.ash",
        "42",
    );
}

#[test]
fn fixed_early_nested_and_handwritten_control_return_44() {
    for name in ["early_nested.ash", "control_nested.ash"] {
        result(&format!("docs/design/macros/fixtures/escapes/{name}"), "44");
    }
}

#[test]
fn fixed_freshness_and_handwritten_control_return_20() {
    for name in ["freshness.ash", "control_freshness.ash"] {
        result(&format!("docs/design/macros/fixtures/escapes/{name}"), "20");
    }
}

#[test]
fn fixed_quote_roundtrip_and_handwritten_control_return_42() {
    for name in ["quote_roundtrip.ash", "control_quote_roundtrip.ash"] {
        result(&format!("docs/design/macros/fixtures/escapes/{name}"), "42");
    }
}

#[test]
fn fixed_quote_type_failures_reach_ordinary_checking() {
    for (name, expected) in [
        ("wrong_hole.ash", TypeReason::Argument),
        ("wrong_code_type.ash", TypeReason::BindingInitializer),
        (
            "control_wrong_code_type.ash",
            TypeReason::BindingInitializer,
        ),
        ("primitive_escape.ash", TypeReason::Argument),
    ] {
        let path = format!("docs/design/macros/fixtures/escapes/{name}");
        let failure =
            compile_path(configuration(&path)).expect_err("the ordinary type mismatch must reject");
        let Some(PipelineFailure::Typing(TypeError::Source(error))) = failure.pipeline_failure()
        else {
            panic!("expected ordinary checking for {name}: {failure:?}");
        };
        assert_eq!(error.reason, expected, "{name}");
    }
}

#[test]
fn unused_quote_names_wait_for_ordinary_output_resolution() {
    result(
        "docs/design/macros/fixtures/escapes/unused_unknown.ash",
        "42",
    );
    let failure = compile_path(configuration(
        "docs/design/macros/fixtures/escapes/invoked_unknown.ash",
    ))
    .expect_err("a surviving unavailable name must reject");
    let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
        panic!("expected ordinary resolution: {failure:?}");
    };
    assert_eq!(error.reason, ResolveReason::UnknownName);
    assert_eq!(error.found.as_deref(), Some("missing"));
}

#[test]
fn reached_ordinary_quotation_without_a_host_refuses_before_publication() {
    for name in ["reached-main.ash", "reached-helper.ash"] {
        let path = format!("tests/fixtures/surface-macros/quote-no-host/{name}");
        let program = compile_path(configuration(&path)).expect("the ordinary source checks");
        let failure = execute(&program).expect_err("a reached quote needs the syntax host");
        assert!(matches!(
            failure.pipeline_failure(),
            Some(PipelineFailure::Runtime(RuntimeFailure::ForeignBinding))
        ));
    }
    result(
        "tests/fixtures/surface-macros/quote-no-host/unused-helper.ash",
        "42",
    );
}
