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
fn generated_token_diagnostics_point_to_the_invocation() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_file_diagnostics, write_human, write_json},
    };

    let valid = compile_path(fixture("template-diagnostic/valid.ash"))
        .expect("valid generated arithmetic still passes Core validation");
    assert_eq!(execute(&valid).unwrap().value_display(), "42");

    let failure = compile_path(fixture("template-diagnostic/invalid.ash"))
        .expect_err("the generated Bool operand is not an Int");
    assert_eq!(failure.reason_code(), "type.operator-operand");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let diagnostic = diagnostics
        .first()
        .expect("the type failure is presentable");
    let mut human = Vec::new();
    write_human(
        &mut human,
        diagnostic,
        &Catalogue::new(Locale::English).unwrap(),
    )
    .unwrap();
    assert!(String::from_utf8(human).unwrap().contains("add_boolean 40"));
    let mut json = Vec::new();
    write_json(&mut json, diagnostic).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    assert_eq!(json["reason"], "type.operator-operand");
    let source = include_str!("fixtures/surface-macros/template-diagnostic/invalid.ash");
    let invocation = "add_boolean 40";
    let start = source.find(invocation).unwrap();
    let labels = json["labels"].as_array().unwrap();
    assert_eq!(labels.len(), 2);
    assert_eq!(labels[0]["relationship"], "operator_operand");
    assert_eq!(labels[1]["relationship"], "operator_requirement");
    for label in labels {
        assert!(label["path"].as_str().unwrap().ends_with("invalid.ash"));
        assert_eq!(label["byte_start"], start);
        assert_eq!(label["byte_end"], start + invocation.len());
    }
}

#[test]
fn template_cleanup_uses_the_ordinary_expression_pipeline() {
    for path in ["template-cleanup/entry.ash", "template-cleanup/unused.ash"] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
}

#[test]
fn nested_template_expansions_resolve_in_order() {
    let compiled = compile_path(fixture("expansion-depth/finite.ash"))
        .expect("finite nested expansions resolve");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
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
fn template_targeted_import_uses_its_owner_despite_caller_shadowing() {
    for path in [
        "qualified-owner/entry_targeted.ash",
        "qualified-owner/entry_targeted_facade.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    let failure = compile_path(fixture("qualified-owner/invalid_targeted_caller.ash"))
        .expect_err("the syntax import does not bind the owner's targeted name");
    assert!(failure.graph_failure().is_none(), "{failure:?}");
}

#[test]
fn template_qualified_import_follows_the_owners_public_facade() {
    let compiled = compile_path(fixture("qualified-owner/entry_facade.ash"))
        .expect("the template keeps the selected facade's original exported member");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_qualified_constructor_uses_its_owner_and_rejects_opaque_constructors() {
    for path in [
        "qualified-constructor/entry.ash",
        "qualified-constructor/entry_same.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for path in [
        "qualified-constructor/invalid_hidden.ash",
        "qualified-constructor/invalid_hidden_pattern.ash",
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert!(failure.graph_failure().is_none(), "{path}: {failure:?}");
    }
}

#[test]
fn template_qualified_constructor_pattern_uses_its_owner() {
    for path in [
        "qualified-constructor/entry_pattern.ash",
        "qualified-constructor/entry_function.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
}

#[test]
fn template_targeted_constructor_uses_its_owner_under_caller_shadowing() {
    for path in [
        "qualified-constructor/entry_targeted.ash",
        "qualified-constructor/entry_targeted_pattern.ash",
        "qualified-constructor/entry_targeted_facade.ash",
        "qualified-constructor/entry_procedural_targeted.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    let failure = compile_path(fixture("qualified-constructor/invalid_targeted_caller.ash"))
        .expect_err("the syntax import does not bind the owner's constructor");
    assert!(failure.graph_failure().is_none(), "{failure:?}");
}

#[test]
fn template_method_uses_caller_evidence_without_importing_owner_implementation() {
    for path in [
        "template-method/entry.ash",
        "template-method/entry_targeted.ash",
        "template-method/entry_qualified.ash",
        "template-method/entry_facade.ash",
        "template-method/entry_procedural.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for path in [
        "template-method/missing_evidence.ash",
        "template-method/missing_targeted_evidence.ash",
        "template-method/missing_qualified_evidence.ash",
        "template-method/missing_facade_evidence.ash",
        "template-method/missing_procedural_evidence.ash",
    ] {
        let failure = compile_path(fixture(path))
            .expect_err("the owner's implementation is not imported with syntax");
        assert_eq!(
            failure.reason_code(),
            "constraint.unsatisfied",
            "{path}: {failure:?}"
        );
    }
    let failure = compile_path(fixture("template-method/caller_cannot_name_method.ash"))
        .expect_err("the syntax import does not bind the method in caller source");
    assert_eq!(failure.reason_code(), "resolve.unknown-name");
}

#[test]
fn template_continuations_use_the_actual_handler_capability() {
    for path in [
        "template-resume/entry.ash",
        "template-resume/procedural.ash",
        "template-resume/discard.ash",
        "template-resume/retain.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }

    for (path, expected) in [
        (
            "template-resume/outside.ash",
            "effect.resume-outside-clause",
        ),
        (
            "template-resume/procedural_outside.ash",
            "effect.resume-outside-clause",
        ),
        (
            "template-resume/nested_function.ash",
            "effect.resume-capture",
        ),
        (
            "template-resume/discard_outside.ash",
            "effect.resume-outside-clause",
        ),
        (
            "template-resume/retain_outside.ash",
            "effect.retain-outside-root",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), expected, "{path}: {failure:?}");
    }
}

#[test]
fn unused_template_checks_direct_names_but_defers_nested_syntax() {
    for path in [
        "template-admission/missing/entry.ash",
        "template-admission/missing_nested/entry.ash",
    ] {
        let failure = compile_path(fixture(path))
            .expect_err("an unused template cannot name a missing defining-module helper");
        assert_eq!(
            failure.reason_code(),
            "resolve.unknown-name",
            "{path}: {failure:?}"
        );
    }
    for path in [
        "template-admission/good/entry.ash",
        "template-admission/good/reuse.ash",
        "template-admission/deferred/entry.ash",
        "nested-identifier/unused.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    let failure = compile_path(fixture("nested-identifier/invalid.ash"))
        .expect_err("a surviving nested free name cannot use a caller helper");
    assert_eq!(failure.reason_code(), "resolve.unknown-name");
}

#[test]
fn nested_syntax_identifier_keeps_the_outer_template_context() {
    let compiled = compile_path(fixture("nested-identifier/entry.ash"))
        .expect("the nested syntax binds the outer template's literal identifier");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_resource_preserves_initializer_body_and_identity_scopes() {
    for path in [
        "template-resource/entry.ash",
        "template-resource/handwritten.ash",
        "template-resource/reversed.ash",
        "template-resource/reversed_handwritten.ash",
        "template-resource/initializer.ash",
        "template-resource/body.ash",
        "template-resource/typed.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, expected) in [
        ("template-resource/escape.ash", "type.resource-escape"),
        (
            "template-resource/missing_builtin.ash",
            "resolve.resource-builtin-required",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), expected, "{path}: {failure:?}");
    }
}

#[test]
fn template_region_preserves_selection_and_access_scope() {
    for path in [
        "template-region/entry.ash",
        "template-region/nested.ash",
        "template-region/typed.ash",
        "template-region/provider.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, expected) in [
        ("template-region/escape.ash", "type.resource-escape"),
        ("template-region/provider_scope.ash", "resolve.unknown-name"),
        ("template-region/outside.ash", "resolve.unknown-name"),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), expected, "{path}: {failure:?}");
    }
}

#[test]
fn template_perform_uses_the_defining_effect_not_the_callers_shadow() {
    for path in [
        "template-perform/entry.ash",
        "template-perform/private.ash",
        "template-perform/private_signature.ash",
        "template-perform/private_nested_signature.ash",
        "template-perform/handler_capture.ash",
        "template-perform/outer_resume.ash",
        "template-perform/captured_resume.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, expected) in [
        (
            "template-perform/wrong_handler.ash",
            "effect.handler-missing-input",
        ),
        ("template-perform/caller_private.ash", "effect.unknown"),
        ("template-perform/private_caller.ash", "effect.unknown"),
        (
            "template-perform/private_signature_type.ash",
            "resolve.unknown-type",
        ),
        (
            "template-perform/private_signature_constructor.ash",
            "resolve.unknown-constructor",
        ),
        (
            "template-perform/private_nested_signature_type.ash",
            "resolve.unknown-type",
        ),
        (
            "template-perform/private_nested_signature_constructor.ash",
            "resolve.unknown-constructor",
        ),
        (
            "template-perform/private_nested_signature_hidden.ash",
            "resolve.unknown-constructor",
        ),
        (
            "template-perform/private_nested.ash",
            "effect.resume-capture",
        ),
        ("template-perform/incomplete.ash", "effect.handler-coverage"),
        ("template-perform/duplicate.ash", "effect.handler-coverage"),
        ("template-perform/unknown/entry.ash", "resolve.unknown-name"),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), expected, "{path}: {failure:?}");
    }
}

#[test]
fn expanded_effects_and_resource_scopes_follow_ordinary_rules() {
    for (path, expected) in [
        ("template-effects/entry.ash", "42"),
        ("template-effects/handwritten.ash", "42"),
        ("template-effects/reversed.ash", "33"),
        ("template-effects/twice.ash", "42"),
        ("template-effects/resource_ok.ash", "42"),
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(
            execute(&compiled).unwrap().value_display(),
            expected,
            "{path}"
        );
    }
    for path in [
        "template-effects/resource_escape.ash",
        "template-effects/resource_escape_handwritten.ash",
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(
            failure.reason_code(),
            "type.resource-escape",
            "{path}: {failure:?}"
        );
    }
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
fn copied_expression_binders_keep_distinct_scopes() {
    let compiled = compile_path(fixture("copied-declarations/binder.ash"))
        .expect("each copy keeps its own binder and use");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn copied_expression_local_newtypes_keep_distinct_scopes() {
    let compiled = compile_path(fixture("copied-declarations/newtype.ash"))
        .expect("each copy keeps its own local newtype and constructor");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn copied_expression_resources_keep_distinct_scopes() {
    for path in [
        "copied-declarations/resource.ash",
        "copied-declarations/resource_foreign.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
}

#[test]
fn copied_expression_preserves_nested_syntax_and_caller_references() {
    let compiled = compile_path(fixture("copied-declarations/combined.ash"))
        .expect("copied declarations and nested syntax preserve the caller reference");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_local_newtype_does_not_capture_the_caller_nominal() {
    let compiled = compile_path(fixture("generated-newtype/entry.ash"))
        .expect("the generated local newtype preserves caller nominal references");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn template_captured_identifier_can_name_a_local_newtype() {
    let compiled = compile_path(fixture("template-newtype-capture/entry.ash"))
        .expect("captured names work in ordinary local declarations");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
    for (path, expected) in [
        (
            "template-newtype-capture/wrong_kind.ash",
            "parse.expected-form",
        ),
        (
            "template-newtype-capture/malformed.ash",
            "parse.expected-operand",
        ),
        (
            "template-newtype-capture/nested_malformed.ash",
            "parse.expected-form",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), expected, "{path}: {failure:?}");
    }
    compile_path(fixture("template-newtype-capture/lowercase.ash"))
        .expect_err("an actual lowercase identifier cannot name a newtype");
}

#[test]
fn invalid_template_output_reports_the_parser_cause() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_file_diagnostics, write_human, write_json},
    };
    let failure = compile_path(fixture("template-newtype-capture/lowercase.ash"))
        .expect_err("a lowercase identifier cannot name a newtype");
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert_eq!(failure.reason_code(), "parse.expected-form");
    let diagnostics = compile_file_diagnostics(&failure).expect("parser cause is presentable");
    let diagnostic = diagnostics.first().expect("a parser diagnostic");
    let mut human = Vec::new();
    write_human(
        &mut human,
        diagnostic,
        &Catalogue::new(Locale::English).unwrap(),
    )
    .unwrap();
    let human = String::from_utf8(human).unwrap();
    assert!(human.contains("lowercase.ash"), "{human}");
    assert!(human.contains("forms.ash"), "{human}");
    let mut json = Vec::new();
    write_json(&mut json, diagnostic).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    assert_eq!(json["reason"], "parse.expected-form");
    let labels = json["labels"].as_array().unwrap();
    assert_eq!(labels[0]["relationship"], "expected_form");
    assert!(
        labels
            .iter()
            .any(|label| label["relationship"] == "syntax_invocation")
    );
    assert!(
        labels
            .iter()
            .any(|label| label["relationship"] == "syntax_definition")
    );
}

#[test]
fn template_captured_identifier_resolves_a_caller_local_type() {
    for path in [
        "template-annotation/captured/entry.ash",
        "template-annotation/captured/local.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, expected) in [
        (
            "template-annotation/captured/wrong_type.ash",
            "type.binding-initializer",
        ),
        (
            "template-annotation/captured/unknown.ash",
            "resolve.unknown-type",
        ),
        (
            "template-annotation/unknown/entry.ash",
            "resolve.unknown-type",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), expected, "{path}: {failure:?}");
    }
}

#[test]
fn template_captured_identifier_applies_a_caller_type_constructor() {
    let compiled = compile_path(fixture("template-annotation/captured/applied.ash"))
        .expect("captured type constructors use caller syntax");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
    for (path, expected) in [
        (
            "template-annotation/captured/applied_wrong.ash",
            "type.binding-initializer",
        ),
        (
            "template-annotation/captured/applied_missing.ash",
            "resolve.unknown-type",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), expected, "{path}: {failure:?}");
    }
}

#[test]
fn template_captured_identifier_selects_a_caller_effect() {
    for path in [
        "template-perform/captured/entry.ash",
        "template-perform/captured/generic.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, expected) in [
        (
            "template-perform/captured/missing_operand.ash",
            "resolve.unknown-name",
        ),
        (
            "template-perform/captured/missing_argument.ash",
            "resolve.unknown-type",
        ),
        (
            "template-perform/captured/wrong_handler.ash",
            "effect.handler-missing-input",
        ),
        (
            "template-perform/captured/unknown_operation.ash",
            "resolve.unknown-name",
        ),
        ("template-perform/unknown/entry.ash", "resolve.unknown-name"),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), expected, "{path}: {failure:?}");
    }
}

#[test]
fn template_captured_identifier_selects_an_effect_operation() {
    for path in [
        "template-perform/captured/operation.ash",
        "template-perform/captured/private.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for path in [
        "template-perform/captured/operation_missing_operand.ash",
        "template-perform/captured/operation_unknown.ash",
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(
            failure.reason_code(),
            "resolve.unknown-name",
            "{path}: {failure:?}"
        );
    }
    let failure = compile_path(fixture("template-perform/captured/private_direct.ash"))
        .expect_err("the syntax import does not expose its owner's private effect");
    assert_eq!(failure.reason_code(), "effect.unknown");
}

#[test]
fn template_captured_identifier_selects_a_handler_effect_or_operation() {
    for path in [
        "template-handler-capture/entry.ash",
        "template-handler-capture/operation.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, expected) in [
        (
            "template-handler-capture/operation_unknown.ash",
            "resolve.unknown-name",
        ),
        (
            "template-handler-capture/missing_body.ash",
            "resolve.unknown-name",
        ),
        (
            "template-handler-capture/missing_handled.ash",
            "resolve.unknown-name",
        ),
        (
            "template-handler-capture/missing_store.ash",
            "resolve.unknown-name",
        ),
        (
            "template-handler-capture/missing_argument.ash",
            "resolve.unknown-type",
        ),
        (
            "template-handler-capture/missing_operation.ash",
            "resolve.unknown-name",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), expected, "{path}: {failure:?}");
    }
}

#[test]
fn template_captured_identifier_selects_an_effect_row_member() {
    for path in [
        "template-row-capture/entry.ash",
        "template-row-capture/manual.ash",
        "template-row-capture/local_evidence_unused.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, reason) in [
        (
            "template-row-capture/missing_argument.ash",
            "resolve.unknown-type",
        ),
        ("template-row-capture/missing_literal.ash", "effect.unknown"),
        ("template-row-capture/unknown_actual.ash", "effect.unknown"),
        (
            "template-row-capture/wrong_actual.ash",
            "effect.row-union-ambiguous",
        ),
        (
            "template-row-capture/manual_wrong.ash",
            "effect.row-union-ambiguous",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), reason, "{path}: {failure:?}");
    }
}

#[test]
fn template_local_evidence_uses_its_owners_private_interface() {
    for path in [
        "template-private-evidence/manual.ash",
        "template-private-evidence/entry.ash",
        "template-private-evidence/shadow.ash",
        "template-private-evidence/closure_entry.ash",
        "template-private-evidence/captured_method.ash",
        "template-private-evidence/qualified_entry.ash",
        "template-private-evidence/qualified_shadow.ash",
        "template-private-evidence/targeted_entry.ash",
        "template-private-evidence/targeted_shadow.ash",
        "template-private-evidence/alias_entry.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, reason) in [
        (
            "template-private-evidence/direct_interface.ash",
            "resolve.unknown-interface",
        ),
        (
            "template-private-evidence/direct_method.ash",
            "resolve.unknown-name",
        ),
        (
            "template-private-evidence/no_evidence.ash",
            "constraint.unsatisfied",
        ),
        (
            "template-private-evidence/wrong_method.ash",
            "evidence.extra-method",
        ),
        (
            "template-private-evidence/conflicting_method_manual.ash",
            "evidence.extra-method",
        ),
        (
            "template-private-evidence/conflicting_method_entry.ash",
            "evidence.extra-method",
        ),
        (
            "template-private-evidence/decoy_method_entry.ash",
            "evidence.extra-method",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), reason, "{path}: {failure:?}");
    }
}

#[test]
fn template_local_evidence_uses_the_checked_public_interface() {
    let compiled = compile_path(fixture("template-private-evidence/public_entry.ash"))
        .expect("generated local evidence uses the selected checked interface");
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
fn template_named_annotation_uses_owner_and_introduced_local_types() {
    for path in [
        "template-annotation/valid.ash",
        "template-annotation/local.ash",
        "template-annotation/unique.ash",
        "template-annotation/generic_local.ash",
        "template-annotation/generic_pair.ash",
        "template-annotation/imported/entry.ash",
        "template-annotation/imported/facade_entry.ash",
        "template-annotation/imported/qualified_entry.ash",
        "template-annotation/imported/qualified_facade_entry.ash",
        "template-annotation/imported/applied_entry.ash",
        "template-annotation/imported/applied_qualified_entry.ash",
        "template-annotation/imported/applied_nested_entry.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
}

#[test]
fn template_named_annotation_does_not_resolve_in_the_caller() {
    for (path, expected) in [
        ("template-annotation/entry.ash", "type.binding-initializer"),
        (
            "template-annotation/generic.ash",
            "type.binding-initializer",
        ),
        (
            "template-annotation/caller_type.ash",
            "resolve.unknown-type",
        ),
        (
            "template-annotation/caller_constructor.ash",
            "resolve.unknown-constructor",
        ),
        (
            "template-annotation/unknown/entry.ash",
            "resolve.unknown-type",
        ),
        ("template-annotation/late.ash", "resolve.unknown-type"),
        (
            "template-annotation/generic_escape.ash",
            "resolve.unknown-type",
        ),
        (
            "template-annotation/imported/wrong_type.ash",
            "type.binding-initializer",
        ),
        (
            "template-annotation/imported/caller_type.ash",
            "resolve.unknown-type",
        ),
        (
            "template-annotation/imported/qualified_wrong.ash",
            "type.binding-initializer",
        ),
        (
            "template-annotation/imported/qualified_caller.ash",
            "resolve.unavailable-export",
        ),
        (
            "template-annotation/imported/private_entry.ash",
            "resolve.unavailable-export",
        ),
        (
            "template-annotation/imported/applied_wrong.ash",
            "type.binding-initializer",
        ),
        (
            "template-annotation/imported/applied_generic.ash",
            "type.binding-initializer",
        ),
        (
            "template-annotation/imported/applied_unknown.ash",
            "resolve.unknown-type",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), expected, "{path}: {failure:?}");
    }
}

#[test]
fn template_primitive_annotation_remains_supported() {
    let compiled = compile_path(fixture("template-only/primitive-annotation.ash"))
        .expect("a primitive annotation needs no definition-site lookup");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}
