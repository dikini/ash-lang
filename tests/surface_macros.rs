use std::path::PathBuf;

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};

fn fixture(name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/surface-macros")
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

#[test]
fn handwritten_graph_observes_the_frozen_value() {
    let compiled = compile_path(fixture("handwritten.ash")).expect("handwritten graph compiles");
    let result = execute(&compiled).expect("handwritten graph executes");
    assert_eq!(result.value_display(), "42");
}

#[test]
fn imported_templates_and_ash_transformer_run_through_the_driver() {
    let handwritten = compile_path(fixture("handwritten.ash")).expect("handwritten graph compiles");
    let expected = execute(&handwritten).expect("handwritten graph executes");
    let expanded = compile_path(fixture("entry.ash")).expect("macro graph compiles");
    let actual = execute(&expanded).expect("macro graph executes");
    assert_eq!(actual.value_display(), expected.value_display());
    assert_eq!(actual.value_display(), "42");
    assert_eq!(actual.type_display(), expected.type_display());
}

#[test]
fn template_macro_preserves_expression_capture_grouping() {
    let compiled = compile_path(fixture("template-only/entry.ash"))
        .expect("the imported template graph compiles");
    let actual = execute(&compiled).expect("the template graph executes");
    assert_eq!(actual.value_display(), "35");
    assert_eq!(actual.type_display(), "Int");
}

#[test]
fn template_function_parameter_keeps_its_introduction_context() {
    let compiled = compile_path(fixture("template-function/hygiene.ash"))
        .expect("the introduced function parameter avoids the caller binding");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_qualified_import_uses_its_owner_despite_caller_alias() {
    let compiled = compile_path(fixture("qualified-owner/entry.ash"))
        .expect("the template keeps its defining module's qualified import");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_qualified_import_follows_the_owners_public_facade() {
    let compiled = compile_path(fixture("qualified-owner/entry_facade.ash"))
        .expect("the template keeps the selected facade's original exported member");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_qualified_import_does_not_expose_dependency_privates_or_caller_aliases() {
    for path in [
        "qualified-owner/invalid_hidden.ash",
        "qualified-owner/invalid_caller.ash",
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert!(failure.graph_failure().is_none(), "{path}: {failure:?}");
    }
}

#[test]
fn captured_function_parameter_binds_the_captured_body() {
    let compiled = compile_path(fixture("template-function/captured.ash"))
        .expect("the captured function parameter scopes over the captured body");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_recursive_members_share_scope_without_capturing_the_caller() {
    let compiled = compile_path(fixture("template-recursive/entry.ash"))
        .expect("the generated recursive group preserves its own and caller contexts");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn captured_recursive_binder_scopes_over_its_initializer_and_body() {
    let compiled = compile_path(fixture("template-recursive/captured.ash"))
        .expect("the captured binder is recursive and does not escape its scope");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn same_spelled_recursive_binders_keep_distinct_contexts() {
    let compiled = compile_path(fixture("template-recursive/mixed.ash"))
        .expect("introduced and captured recursive names remain distinct");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn recursive_binder_splice_requires_an_identifier_capture() {
    let failure = compile_path(fixture("template-recursive/invalid.ash")).unwrap_err();
    assert!(failure.graph_failure().is_none(), "{failure:?}");
    assert_eq!(failure.reason_code(), "resolve.internal-state");
}

#[test]
fn sequential_captured_binders_enter_scope_only_after_their_initializer() {
    let compiled = compile_path(fixture("template-sequential/entry.ash"))
        .expect("captured binders respect sequential initializer scope");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn renamed_template_macro_uses_the_selected_export() {
    let compiled = compile_path(fixture("template-only/renamed.ash"))
        .expect("the renamed syntax graph compiles");
    assert_eq!(execute(&compiled).unwrap().value_display(), "35");
}

#[test]
fn selected_template_without_capture_is_a_syntax_error() {
    let failure = compile_path(fixture("template-only/malformed.ash")).unwrap_err();
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert!(matches!(
        failure.graph_failure(),
        Some(ash::module::LoadGraphError::Syntax(_))
    ));
}

#[test]
fn template_graph_preserves_bindings_and_private_helpers() {
    let compiled =
        compile_path(fixture("template-graph/entry.ash")).expect("the template graph compiles");
    let actual = execute(&compiled).expect("the template graph executes");
    assert_eq!(actual.value_display(), "42");
    assert_eq!(actual.type_display(), "Int");
}

#[test]
fn template_with_literal_separators_selects_the_captured_branch() {
    let compiled = compile_path(fixture("template-graph/choose.ash"))
        .expect("the multi-capture template graph compiles");
    assert_eq!(execute(&compiled).unwrap().value_display(), "35");
}

#[test]
fn nested_template_matchers_keep_their_own_literal_boundaries() {
    let compiled = compile_path(fixture("template-graph/nested-choose.ash"))
        .expect("nested template graph compiles");
    assert_eq!(execute(&compiled).unwrap().value_display(), "35");
}

#[test]
fn captured_identifier_binds_the_captured_expression() {
    let compiled = compile_path(fixture("template-binder/entry.ash"))
        .expect("a captured identifier binds its body");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn introduced_template_binder_does_not_capture_the_caller() {
    let compiled = compile_path(fixture("template-hygiene/entry.ash"))
        .expect("the template keeps its introduced binder private");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_uses_its_defining_modules_syntax_imports() {
    let compiled = compile_path(fixture("template-imported-syntax/entry.ash"))
        .expect("the template can use its own syntax import");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_calls_its_private_helper_without_caller_shadowing() {
    let compiled = compile_path(fixture("template-private/entry.ash"))
        .expect("the template can call its private helper");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
    let failure = compile_path(fixture("template-private/direct.ash")).unwrap_err();
    assert!(failure.is_source_rejection(), "{failure:?}");
}

#[test]
fn template_private_constructor_preserves_an_opaque_reexport() {
    let compiled = compile_path(fixture("template-graph/opaque-reexport.ash"))
        .expect("using syntax must preserve the opaque re-export");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_private_constructor_keeps_ordinary_coverage_opaque() {
    let failure = compile_path(fixture("template-graph/opaque-diagnostic.ash")).unwrap_err();
    match failure.pipeline_failure() {
        Some(ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(
            diagnostic,
        ))) => {
            assert_eq!(diagnostic.reason, ash::elaborate::TypeReason::NonExhaustive);
            assert_eq!(diagnostic.found.as_deref(), Some("(_, false)"));
        }
        other => panic!("expected an ordinary coverage diagnostic, got {other:?}"),
    }
}

#[test]
fn template_operator_separator_stops_the_expression_capture() {
    let compiled = compile_path(fixture("template-only/operator.ash"))
        .expect("the operator separates the expression captures");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_operator_separator_preserves_grouped_operators() {
    let compiled = compile_path(fixture("template-only/operator-group.ash"))
        .expect("an operator inside parentheses stays in the first capture");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_named_annotation_does_not_resolve_in_the_caller() {
    let failure = compile_path(fixture("template-annotation/entry.ash"))
        .expect_err("a definition-site named annotation must not use the caller's type");
    assert!(matches!(
        failure.pipeline_failure(),
        Some(ash::driver::PipelineFailure::Resolution(_))
    ));
}

#[test]
fn template_primitive_annotation_remains_supported() {
    let compiled = compile_path(fixture("template-only/primitive-annotation.ash"))
        .expect("a primitive annotation needs no definition-site lookup");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}
