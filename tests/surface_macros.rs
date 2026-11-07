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
fn acceptance_graph_preserves_context_and_effect_count_for_both_authoring_forms() {
    for path in [
        "entry_acceptance_computed.ash",
        "entry_acceptance_template.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        let observation = execute(&compiled).expect(path);
        assert_eq!(observation.value_display(), "42", "{path}");
        assert_eq!(observation.type_display(), "Int", "{path}");
    }
}

#[test]
fn imported_if_preserves_boundaries_nesting_and_line_endings() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    let lf = include_str!("fixtures/surface-macros/entry_acceptance_if.ash");
    let crlf = include_str!("fixtures/surface-macros/entry_acceptance_if_crlf.ash");
    assert!(crlf.contains("\r\n"));
    assert_eq!(crlf.replace("\r\n", "\n"), lf);
    for path in [
        "entry_acceptance_if.ash",
        "entry_acceptance_if_crlf.ash",
        "entry_acceptance_if_precedence.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for path in [
        "entry_acceptance_if_missing_separator.ash",
        "entry_acceptance_if_missing_capture.ash",
        "entry_acceptance_if_application.ash",
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), "parse.expected-form", "{path}");
    }
    let source = include_str!("fixtures/surface-macros/entry_acceptance_if_wrong_type.ash");
    let failure = compile_path(fixture("entry_acceptance_if_wrong_type.ash"))
        .expect_err("the generated match requires Bool");
    assert_eq!(failure.reason_code(), "pattern.type-mismatch");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let value = source.find("42").unwrap();
    assert_eq!(json["labels"][0]["relationship"], "match_value");
    assert_eq!(json["labels"][0]["byte_start"], value);
    assert_eq!(json["labels"][0]["byte_end"], value + 2);
    assert!(
        json["facts"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fact| { fact["name"] == "pattern_requirement" && fact["value"] == "Bool" })
    );
}

#[test]
fn definition_context_keeps_private_helpers_and_types_through_linking() {
    for path in [
        "core-authority/entry.ash",
        "definition-constructor/entry.ash",
        "definition-nominal/entry.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
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
fn qualified_names_follow_the_captured_or_defining_alias_context() {
    for path in [
        "qualified-capture/type_caller.ash",
        "qualified-capture/type_owner.ash",
        "qualified-capture/term_caller.ash",
        "qualified-capture/term_owner.ash",
        "qualified-capture/constructor_owner.ash",
        "qualified-capture/constructor_caller.ash",
        "qualified-capture/unused_missing_alias.ash",
        "qualified-capture/unused_missing_operand.ash",
        "qualified-capture/unused_missing_argument.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, reason) in [
        (
            "qualified-capture/invoked_missing_alias.ash",
            "resolve.unavailable-export",
        ),
        (
            "qualified-capture/withheld_member.ash",
            "resolve.unavailable-export",
        ),
        (
            "qualified-capture/withheld_type.ash",
            "resolve.unavailable-export",
        ),
        (
            "qualified-capture/opaque_constructor.ash",
            "resolve.opaque-constructor",
        ),
        (
            "qualified-capture/fresh_alias.ash",
            "resolve.unavailable-export",
        ),
        (
            "qualified-capture/lowercase_alias.ash",
            "parse.unexpected-token",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), reason, "{path}: {failure:?}");
    }
}

#[test]
fn qualified_effects_follow_their_alias_context() {
    for path in [
        "qualified-effect/manual.ash",
        "qualified-effect/owner.ash",
        "qualified-effect/wrapped.ash",
        "qualified-effect/caller_capture.ash",
        "qualified-effect/owner_capture.ash",
        "qualified-effect/handler_caller.ash",
        "qualified-effect/handler_owner.ash",
        "qualified-effect/row_caller.ash",
        "qualified-effect/row_owner.ash",
        "qualified-effect/facade.ash",
        "qualified-effect/both_captured.ash",
        "qualified-effect/parameterized.ash",
        "qualified-effect/missing_operation.ash",
        "qualified-effect/missing_alias.ash",
        "qualified-effect/missing_operand.ash",
        "qualified-effect/missing_argument.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, reason) in [
        (
            "qualified-effect/invoked_missing_operation.ash",
            "resolve.unknown-name",
        ),
        ("qualified-effect/private.ash", "effect.unknown"),
        ("qualified-effect/wrong_kind.ash", "effect.kind"),
        (
            "qualified-effect/lowercase_effect.ash",
            "parse.expected-operand",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), reason, "{path}: {failure:?}");
    }
}

#[test]
fn targeted_and_generic_owner_effects_keep_their_checked_identity() {
    for path in [
        "qualified-effect/targeted_manual.ash",
        "qualified-effect/targeted_entry.ash",
        "qualified-effect/targeted_generic.ash",
        "qualified-effect/targeted_facade.ash",
        "qualified-effect/owner_generic_manual.ash",
        "qualified-effect/owner_generic_entry.ash",
        "qualified-effect/owner_generic_private.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, reason) in [
        ("qualified-effect/targeted_caller.ash", "effect.unknown"),
        (
            "qualified-effect/targeted_private.ash",
            "resolve.unavailable-export",
        ),
        (
            "qualified-effect/owner_generic_caller.ash",
            "effect.unknown",
        ),
        (
            "qualified-effect/wrong_arity.ash",
            "effect.handler-coverage",
        ),
        (
            "qualified-effect/wrong_arity_manual.ash",
            "effect.handler-coverage",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), reason, "{path}: {failure:?}");
    }
}

#[test]
fn captured_qualified_interfaces_use_the_alias_context() {
    for path in [
        "qualified-interface/manual.ash",
        "qualified-interface/caller.ash",
        "qualified-interface/owner.ash",
        "qualified-interface/missing_alias.ash",
        "qualified-interface/missing_argument.ash",
        "qualified-interface/missing_body.ash",
        "qualified-interface/pattern_escape.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, reason) in [
        (
            "qualified-interface/invoked_missing_body.ash",
            "resolve.unknown-name",
        ),
        (
            "qualified-interface/wrong_kind.ash",
            "resolve.interface-kind",
        ),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), reason, "{path}: {failure:?}");
    }
}

#[test]
fn captured_effect_inside_an_owner_row_argument_uses_the_caller_effect() {
    for path in [
        "row-argument/manual.ash",
        "row-argument/entry.ash",
        "row-argument/owner_entry.ash",
        "row-argument/missing_member.ash",
        "row-argument/missing_member_first.ash",
        "row-argument/missing_argument.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    let path = "row-argument/wrong_kind.ash";
    let failure = compile_path(fixture(path)).expect_err(path);
    assert_eq!(failure.reason_code(), "effect.kind", "{path}: {failure:?}");
}

#[test]
fn captured_row_tails_use_the_callers_contextual_parameter() {
    for path in [
        "row-tail/manual.ash",
        "row-tail/entry.ash",
        "row-tail/manual_row.ash",
        "row-tail/entry_row.ash",
        "row-tail/entry_forwarded.ash",
        "row-tail/missing_literal.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for path in [
        "row-tail/missing_actual.ash",
        "row-tail/entry_introduced_miss.ash",
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), "resolve.unknown-type", "{path}");
    }
    let manual = compile_path(fixture("row-tail/wrong_kind_manual.ash"))
        .expect_err("a Type parameter cannot be an effect-row tail");
    let generated = compile_path(fixture("row-tail/wrong_kind.ash"))
        .expect_err("the generated tail must keep the same kind check");
    assert_eq!(generated.reason_code(), manual.reason_code());
}

#[test]
fn captured_pattern_constructors_keep_their_lookup_context() {
    for path in [
        "captured-pattern/manual.ash",
        "captured-pattern/entry.ash",
        "captured-pattern/entry_caller.ash",
        "captured-pattern/entry_name.ash",
        "captured-pattern/manual_nullary.ash",
        "captured-pattern/entry_nullary.ash",
        "captured-pattern/missing_alias.ash",
        "captured-pattern/missing_payload.ash",
        "captured-pattern/duplicate.ash",
        "captured-pattern/binder_escape.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, reason) in [
        (
            "captured-pattern/invoked_missing_payload.ash",
            "resolve.unknown-constructor",
        ),
        ("captured-pattern/opaque.ash", "resolve.opaque-constructor"),
        (
            "captured-pattern/entry_duplicate.ash",
            "pattern.duplicate-binder",
        ),
        ("captured-pattern/lowercase.ash", "parse.expected-form"),
    ] {
        let failure = compile_path(fixture(path)).expect_err(path);
        assert_eq!(failure.reason_code(), reason, "{path}: {failure:?}");
    }
}

#[test]
fn generated_token_diagnostics_preserve_definition_and_invocation() {
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
    let human = String::from_utf8(human).unwrap();
    assert!(human.contains("add_boolean 40"), "{human}");
    assert!(human.contains("true"), "{human}");
    let mut json = Vec::new();
    write_json(&mut json, diagnostic).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    assert_eq!(json["reason"], "type.operator-operand");
    let source = include_str!("fixtures/surface-macros/template-diagnostic/invalid.ash");
    let definition = include_str!("fixtures/surface-macros/template-diagnostic/forms.ash");
    let invocation = "add_boolean 40";
    let start = source.find(invocation).unwrap();
    let labels = json["labels"].as_array().unwrap();
    assert_eq!(labels[0]["relationship"], "operator_operand");
    assert_eq!(labels[1]["relationship"], "operator_requirement");
    assert!(labels[0]["path"].as_str().unwrap().ends_with("forms.ash"));
    let operand = definition.find("true").unwrap();
    assert_eq!(labels[0]["byte_start"], operand);
    assert_eq!(labels[0]["byte_end"], operand + "true".len());
    assert!(labels[1]["path"].as_str().unwrap().ends_with("forms.ash"));
    let operator = definition.find('+').unwrap();
    assert_eq!(labels[1]["byte_start"], operator);
    assert_eq!(labels[1]["byte_end"], operator + 1);
    assert!(labels.iter().any(|label| {
        label["relationship"] == "syntax_invocation"
            && label["path"].as_str().unwrap().ends_with("invalid.ash")
            && label["byte_start"] == start
            && label["byte_end"] == start + invocation.len()
    }));
    assert!(labels.iter().any(|label| {
        label["relationship"] == "syntax_definition"
            && label["path"].as_str().unwrap().ends_with("forms.ash")
    }));
}

#[test]
fn nested_identifier_capture_preserves_combined_origin() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_file_diagnostics, write_human, write_json},
    };

    for entry in ["entry.ash", "forwarded.ash"] {
        let failure = compile_path(fixture(&format!("identifier-origin/{entry}")))
            .expect_err("the nested transformer rejects its identifier");
        assert_eq!(failure.reason_code(), "syntax.rejected");
        let diagnostics = compile_file_diagnostics(&failure).unwrap();
        let mut json = Vec::new();
        write_json(&mut json, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
        let labels = json["labels"].as_array().unwrap();
        assert!(labels[0]["path"].as_str().unwrap().ends_with(entry));
        assert!(
            labels.iter().any(|label| {
                label["relationship"] == "syntax_cause"
                    && label["path"].as_str().unwrap().ends_with("outer.ash")
            }),
            "{entry}: {json}"
        );
        assert!(
            labels.iter().any(|label| {
                label["relationship"] == "syntax_definition"
                    && label["path"].as_str().unwrap().ends_with("inner.ash")
            }),
            "{entry}: {json}"
        );
        let mut human = Vec::new();
        write_human(
            &mut human,
            &diagnostics[0],
            &Catalogue::new(Locale::English).unwrap(),
        )
        .unwrap();
        let human = String::from_utf8(human).unwrap();
        assert!(
            human.contains("outer.ash") && human.contains("inner.ash"),
            "{human}"
        );
    }
}

#[test]
fn unresolved_nested_identifier_preserves_combined_causes() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_file_diagnostics, write_human, write_json},
    };

    let failure = compile_path(fixture("identifier-origin/resolve.ash"))
        .expect_err("the returned caller name is not bound");
    assert_eq!(failure.reason_code(), "resolve.unknown-name");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    let entry = include_str!("fixtures/surface-macros/identifier-origin/resolve.ash");
    let invocation = "outer_resolve 42";
    let invocation_start = entry.find(invocation).unwrap();
    assert_eq!(labels[0]["relationship"], "unresolved_name");
    assert!(labels[0]["path"].as_str().unwrap().ends_with("resolve.ash"));
    assert_eq!(labels[0]["byte_start"], invocation_start);
    assert_eq!(labels[0]["byte_end"], invocation_start + invocation.len());
    let outer = include_str!("fixtures/surface-macros/identifier-origin/outer.ash");
    let definition = "pub syntax outer_resolve $value:expr => using expand_resolve";
    let definition_start = outer.find(definition).unwrap();
    let causes: Vec<_> = labels
        .iter()
        .filter(|label| label["relationship"] == "syntax_cause")
        .collect();
    assert_eq!(causes.len(), 1, "{json}");
    assert!(causes[0]["path"].as_str().unwrap().ends_with("outer.ash"));
    assert_eq!(causes[0]["byte_start"], definition_start);
    assert_eq!(causes[0]["byte_end"], definition_start + definition.len());
    let inner = include_str!("fixtures/surface-macros/identifier-origin/inner.ash");
    let inner_definition = "pub syntax observe_resolve $name:ident = $value:expr => using emit";
    let inner_start = inner.find(inner_definition).unwrap();
    let frames: Vec<_> = labels
        .iter()
        .filter(|label| {
            label["relationship"] == "syntax_invocation"
                || label["relationship"] == "syntax_definition"
        })
        .collect();
    assert_eq!(frames.len(), 4, "{json}");
    for frame in [frames[0], frames[2]] {
        assert_eq!(frame["relationship"], "syntax_invocation", "{json}");
        assert!(frame["path"].as_str().unwrap().ends_with("resolve.ash"));
        assert_eq!(frame["byte_start"], invocation_start);
        assert_eq!(frame["byte_end"], invocation_start + invocation.len());
    }
    assert_eq!(frames[1]["relationship"], "syntax_definition");
    assert!(
        frames[1]["path"].as_str().unwrap().ends_with("outer.ash"),
        "{json}"
    );
    assert_eq!(frames[1]["byte_start"], definition_start);
    assert_eq!(frames[1]["byte_end"], definition_start + definition.len());
    assert_eq!(frames[3]["relationship"], "syntax_definition");
    assert!(frames[3]["path"].as_str().unwrap().ends_with("inner.ash"));
    assert_eq!(frames[3]["byte_start"], inner_start);
    assert_eq!(frames[3]["byte_end"], inner_start + inner_definition.len());
    for (locale, expected) in [
        (
            Locale::English,
            "This location contributed to the rejection.",
        ),
        (Locale::Bulgarian, "Това място допринесе за отхвърлянето."),
    ] {
        let mut human = Vec::new();
        write_human(
            &mut human,
            &diagnostics[0],
            &Catalogue::new(locale).unwrap(),
        )
        .unwrap();
        assert!(String::from_utf8(human).unwrap().contains(expected));
    }
}

#[test]
fn application_failure_preserves_function_occurrence() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    let forms = include_str!("fixtures/surface-macros/template-diagnostic/application_forms.ash");
    let capture =
        include_str!("fixtures/surface-macros/template-diagnostic/application_capture.ash");
    for (entry, source, source_file, marker) in [
        (
            "application_invalid.ash",
            forms,
            "application_forms.ash",
            "1 $value",
        ),
        (
            "application_capture.ash",
            capture,
            "application_capture.ash",
            "1 with 42",
        ),
    ] {
        let failure = compile_path(fixture(&format!("template-diagnostic/{entry}")))
            .expect_err("an Int is not a function");
        assert_eq!(failure.reason_code(), "type.not-applicable");
        let diagnostics = compile_file_diagnostics(&failure).unwrap();
        let mut json = Vec::new();
        write_json(&mut json, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
        let labels = json["labels"].as_array().unwrap();
        let position = source.find(marker).unwrap();
        assert_eq!(labels[0]["relationship"], "application_function");
        assert!(labels[0]["path"].as_str().unwrap().ends_with(source_file));
        assert_eq!(labels[0]["byte_start"], position);
        assert_eq!(labels[0]["byte_end"], position + 1);
        for relationship in ["syntax_invocation", "syntax_definition"] {
            assert_eq!(
                labels
                    .iter()
                    .filter(|label| label["relationship"] == relationship)
                    .count(),
                1,
                "{entry}: {json}"
            );
        }
    }
    let valid = compile_path(fixture("template-diagnostic/application_valid.ash")).unwrap();
    assert_eq!(execute(&valid).unwrap().value_display(), "42");
}

#[test]
fn application_argument_failure_preserves_function_and_argument_causes() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    let forms = include_str!("fixtures/surface-macros/template-diagnostic/application_forms.ash");
    let capture = include_str!(
        "fixtures/surface-macros/template-diagnostic/application_argument_capture.ash"
    );
    for (entry, function_source, function_file, function_marker) in [
        (
            "application_argument.ash",
            forms,
            "application_forms.ash",
            "helper $value",
        ),
        (
            "application_argument_capture.ash",
            capture,
            "application_argument_capture.ash",
            "increment with true",
        ),
    ] {
        let failure = compile_path(fixture(&format!("template-diagnostic/{entry}")))
            .expect_err("the Bool argument does not match Int");
        assert_eq!(failure.reason_code(), "type.argument");
        let diagnostics = compile_file_diagnostics(&failure).unwrap();
        let mut json = Vec::new();
        write_json(&mut json, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
        let labels = json["labels"].as_array().unwrap();
        let start = function_source.find(function_marker).unwrap();
        let end = start + function_marker.split_whitespace().next().unwrap().len();
        assert_eq!(labels[0]["relationship"], "argument");
        assert!(labels[0]["path"].as_str().unwrap().ends_with(entry));
        assert!(
            labels
                .iter()
                .any(|label| label["relationship"] == "function_domain")
        );
        assert!(
            labels.iter().any(|label| {
                label["relationship"] == "syntax_cause"
                    && label["path"].as_str().unwrap().ends_with(function_file)
                    && label["byte_start"] == start
                    && label["byte_end"] == end
            }),
            "{entry}: {json}"
        );
    }
}

#[test]
fn captured_expression_diagnostics_preserve_source_and_invocation() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    let failure = compile_path(fixture("template-diagnostic/captured_invalid.ash"))
        .expect_err("the captured Bool operand is not an Int");
    assert_eq!(failure.reason_code(), "type.operator-operand");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    let source = include_str!("fixtures/surface-macros/template-diagnostic/captured_invalid.ash");
    let operand = source.find("true").unwrap();
    assert_eq!(labels[0]["relationship"], "operator_operand");
    assert!(
        labels[0]["path"]
            .as_str()
            .unwrap()
            .ends_with("captured_invalid.ash")
    );
    assert_eq!(labels[0]["byte_start"], operand);
    assert_eq!(labels[0]["byte_end"], operand + "true".len());
    let operator = source.find('+').unwrap();
    let operator_label = labels
        .iter()
        .find(|label| label["relationship"] == "operator_requirement")
        .unwrap();
    assert_eq!(operator_label["byte_start"], operator);
    assert_eq!(operator_label["byte_end"], operator + 1);
    assert!(labels.iter().any(|label| {
        label["relationship"] == "syntax_invocation"
            && label["path"]
                .as_str()
                .unwrap()
                .ends_with("captured_invalid.ash")
    }));
    assert!(labels.iter().any(|label| {
        label["relationship"] == "syntax_definition"
            && label["path"].as_str().unwrap().ends_with("forms.ash")
    }));
}

#[test]
fn match_pattern_failure_preserves_the_captured_value_and_pattern() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_file_diagnostics, write_human, write_json},
    };

    let valid = compile_path(fixture("template-diagnostic/match_value_valid.ash")).unwrap();
    assert_eq!(execute(&valid).unwrap().value_display(), "42");

    let path = "template-diagnostic/match_value_invalid.ash";
    let caller =
        include_str!("fixtures/surface-macros/template-diagnostic/match_value_invalid.ash");
    let forms = include_str!("fixtures/surface-macros/template-diagnostic/match_value_forms.ash");
    let failure = compile_path(fixture(path)).expect_err("an Int cannot match a Bool pattern");
    assert_eq!(failure.reason_code(), "pattern.type-mismatch");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    let value = caller.find("check 42").unwrap() + "check ".len();
    assert_eq!(labels[0]["relationship"], "match_value");
    assert_eq!(labels[0]["byte_start"], value, "{json}");
    assert_eq!(labels[0]["byte_end"], value + 2, "{json}");
    let pattern = forms.find("true").unwrap();
    assert!(
        labels.iter().any(|label| {
            label["relationship"] == "pattern"
                && label["path"]
                    .as_str()
                    .unwrap()
                    .ends_with("match_value_forms.ash")
                && label["byte_start"] == pattern
                && label["byte_end"] == pattern + 4
        }),
        "{json}"
    );
    for relationship in ["syntax_invocation", "syntax_definition"] {
        assert!(
            labels
                .iter()
                .any(|label| label["relationship"] == relationship),
            "{json}"
        );
    }
    for (name, value) in [("expected_type", "Int"), ("pattern_requirement", "Bool")] {
        assert!(
            json["facts"]
                .as_array()
                .unwrap()
                .iter()
                .any(|fact| fact["name"] == name && fact["value"] == value),
            "{json}"
        );
    }
    let mut human = Vec::new();
    write_human(
        &mut human,
        &diagnostics[0],
        &Catalogue::new(Locale::English).unwrap(),
    )
    .unwrap();
    let human = String::from_utf8(human).unwrap();
    assert!(human.contains("This value cannot be matched by the pattern."));
    assert!(human.contains("This pattern requires a value of type `Bool`"));
    assert!(human.contains("true => 42"));

    let manual = compile_path(fixture("template-diagnostic/match_value_manual.ash"))
        .expect_err("the ordinary match also rejects this pattern");
    assert_eq!(manual.reason_code(), "pattern.type-mismatch");
    let diagnostics = compile_file_diagnostics(&manual).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let source = include_str!("fixtures/surface-macros/template-diagnostic/match_value_manual.ash");
    assert_eq!(
        json["labels"][0]["byte_start"],
        source.find("true").unwrap()
    );
    assert_eq!(json["labels"][0]["relationship"], "pattern");
}

#[test]
fn nested_match_pattern_failure_labels_the_leaf_without_mistyping_the_captured_tuple() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_file_diagnostics, write_human, write_json},
    };

    let valid = compile_path(fixture("template-diagnostic/match_value_tuple_valid.ash")).unwrap();
    assert_eq!(execute(&valid).unwrap().value_display(), "42");

    let caller =
        include_str!("fixtures/surface-macros/template-diagnostic/match_value_tuple_invalid.ash");
    let forms = include_str!("fixtures/surface-macros/template-diagnostic/match_value_forms.ash");
    let failure = compile_path(fixture("template-diagnostic/match_value_tuple_invalid.ash"))
        .expect_err("the tuple's Int member cannot match a Bool pattern");
    assert_eq!(failure.reason_code(), "pattern.type-mismatch");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    let value = caller.find("(42, true)").unwrap();
    assert_eq!(labels[0]["relationship"], "match_value");
    assert_eq!(labels[0]["byte_start"], value, "{json}");
    assert_eq!(labels[0]["byte_end"], value + "(42, true)".len(), "{json}");
    assert_eq!(labels[0]["facts"].as_array().unwrap().len(), 0, "{json}");
    let pattern = forms.find("(true, _)").unwrap() + 1;
    let leaf = labels
        .iter()
        .find(|label| {
            label["relationship"] == "pattern"
                && label["byte_start"] == pattern
                && label["byte_end"] == pattern + 4
        })
        .unwrap_or_else(|| panic!("missing leaf pattern: {json}"));
    for (name, value) in [("expected_type", "Int"), ("pattern_requirement", "Bool")] {
        assert!(
            leaf["facts"]
                .as_array()
                .unwrap()
                .iter()
                .any(|fact| { fact["name"] == name && fact["value"] == value }),
            "{json}"
        );
    }
    for (locale, message, requirement) in [
        (
            Locale::English,
            "This value cannot be matched by the pattern.",
            "This pattern requires a value of type `Bool`",
        ),
        (
            Locale::Bulgarian,
            "Тази стойност не може да бъде съпоставена с шаблона.",
            "Този шаблон изисква стойност от тип `Bool`",
        ),
    ] {
        let mut human = Vec::new();
        write_human(
            &mut human,
            &diagnostics[0],
            &Catalogue::new(locale).unwrap(),
        )
        .unwrap();
        let human = String::from_utf8(human).unwrap();
        assert!(human.contains(message));
        assert!(human.contains(requirement));
    }
}

#[test]
fn captured_match_pattern_keeps_its_own_source_and_inherited_frame() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    let source =
        include_str!("fixtures/surface-macros/template-diagnostic/captured_match_pattern.ash");
    let failure = compile_path(fixture("template-diagnostic/captured_match_pattern.ash"))
        .expect_err("the caller's Boolean pattern does not match Int");
    assert_eq!(failure.reason_code(), "pattern.type-mismatch");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    let pattern = source.find("true").unwrap();
    assert_eq!(labels[0]["relationship"], "pattern");
    assert!(
        labels[0]["path"]
            .as_str()
            .unwrap()
            .ends_with("captured_match_pattern.ash")
    );
    assert_eq!(labels[0]["byte_start"], pattern, "{json}");
    assert_eq!(labels[0]["byte_end"], pattern + 4, "{json}");
    for relationship in ["syntax_invocation", "syntax_definition"] {
        assert_eq!(
            labels
                .iter()
                .filter(|label| label["relationship"] == relationship)
                .count(),
            1,
            "{json}"
        );
    }
}

#[test]
fn match_mismatch_preserves_both_captured_causes() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    for (entry, source, invocation, first, second, expected, found) in [
        (
            "match_invalid.ash",
            include_str!("fixtures/surface-macros/template-diagnostic/match_invalid.ash"),
            "branches 1 else true",
            "1",
            "true",
            "Int",
            "Bool",
        ),
        (
            "match_reverse.ash",
            include_str!("fixtures/surface-macros/template-diagnostic/match_reverse.ash"),
            "branches true else 1",
            "true",
            "1",
            "Bool",
            "Int",
        ),
    ] {
        let failure = compile_path(fixture(&format!("template-diagnostic/{entry}")))
            .expect_err("the match arms have different types");
        assert_eq!(failure.reason_code(), "type.mismatch");
        let diagnostics = compile_file_diagnostics(&failure).unwrap();
        let mut json = Vec::new();
        write_json(&mut json, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
        let facts = json["facts"].as_array().unwrap();
        for (name, value) in [("expected", expected), ("found", found)] {
            assert!(
                facts
                    .iter()
                    .any(|fact| fact["name"] == name && fact["value"] == value)
            );
        }
        let invocation_start = source.find(invocation).unwrap();
        let first_start = invocation_start + invocation.find(first).unwrap();
        let second_start = invocation_start + invocation.rfind(second).unwrap();
        let labels = json["labels"].as_array().unwrap();
        assert_eq!(labels[0]["byte_start"], second_start);
        assert_eq!(labels[0]["byte_end"], second_start + second.len());
        assert!(
            labels.iter().any(|label| {
                label["relationship"] == "syntax_cause"
                    && label["path"].as_str().unwrap().ends_with(entry)
                    && label["byte_start"] == first_start
                    && label["byte_end"] == first_start + first.len()
            }),
            "{entry}: {json}"
        );
        assert_eq!(
            labels
                .iter()
                .filter(|label| label["relationship"] == "syntax_cause")
                .count(),
            1,
            "{entry}: {json}"
        );
        for relationship in ["syntax_invocation", "syntax_definition"] {
            assert_eq!(
                labels
                    .iter()
                    .filter(|label| label["relationship"] == relationship)
                    .count(),
                1,
                "{entry}: {json}"
            );
        }
    }

    let valid = compile_path(fixture("template-diagnostic/match_valid.ash")).unwrap();
    assert_eq!(execute(&valid).unwrap().value_display(), "42");
}

#[test]
fn match_function_failure_preserves_first_captured_cause() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    let path = "template-diagnostic/match_function.ash";
    let source = include_str!("fixtures/surface-macros/template-diagnostic/match_function.ash");
    let failure = compile_path(fixture(path)).expect_err("Int cannot provide a function context");
    assert_eq!(failure.reason_code(), "type.function-needs-context");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    let function = source.find("fn(value)").unwrap();
    let first = source.find("branches 1").unwrap() + "branches ".len();
    assert_eq!(labels[0]["byte_start"], function);
    assert!(
        labels.iter().any(|label| {
            label["relationship"] == "syntax_cause"
                && label["byte_start"] == first
                && label["byte_end"] == first + 1
        }),
        "{json}"
    );
}

#[test]
fn match_function_pattern_failure_preserves_first_captured_cause() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    let path = "template-diagnostic/match_pattern.ash";
    let source = include_str!("fixtures/surface-macros/template-diagnostic/match_pattern.ash");
    let failure = compile_path(fixture(path)).expect_err("Bool pattern cannot match Int");
    assert_eq!(failure.reason_code(), "pattern.type-mismatch");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    let pattern = source.find("fn(true)").unwrap() + "fn(".len();
    let first = source.find("branches id").unwrap() + "branches ".len();
    assert_eq!(labels[0]["byte_start"], pattern);
    assert!(
        labels.iter().any(|label| {
            label["relationship"] == "syntax_cause"
                && label["byte_start"] == first
                && label["byte_end"] == first + 2
        }),
        "{json}"
    );
}

#[test]
fn match_mismatch_preserves_procedural_expression_origin() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    let failure = compile_path(fixture("template-diagnostic/match_marked.ash"))
        .expect_err("the marked Bool differs from the first Int arm");
    assert_eq!(failure.reason_code(), "type.mismatch");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    let source = include_str!("fixtures/surface-macros/template-diagnostic/match_marked.ash");
    let first = source.find("branches 1").unwrap() + "branches ".len();
    assert!(
        labels.iter().any(|label| {
            label["relationship"] == "syntax_cause"
                && label["path"]
                    .as_str()
                    .unwrap()
                    .ends_with("match_marked.ash")
                && label["byte_start"] == first
                && label["byte_end"] == first + 1
        }),
        "{json}"
    );
    assert!(
        labels.iter().any(|label| {
            label["relationship"] == "syntax_cause"
                && label["path"]
                    .as_str()
                    .unwrap()
                    .ends_with("match_marked_forms.ash")
        }),
        "{json}"
    );
    assert_eq!(
        labels
            .iter()
            .filter(|label| label["relationship"] == "syntax_invocation")
            .count(),
        2,
        "{json}"
    );
}

#[test]
fn match_mismatch_preserves_combined_first_arm_origins() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    let failure = compile_path(fixture("template-diagnostic/match_combined.ash"))
        .expect_err("the generated Bool differs from the second Int arm");
    assert_eq!(failure.reason_code(), "type.mismatch");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    let causes: Vec<_> = labels
        .iter()
        .filter(|label| label["relationship"] == "syntax_cause")
        .collect();
    assert_eq!(causes.len(), 3, "{json}");
    assert!(
        causes[0]["path"]
            .as_str()
            .unwrap()
            .ends_with("match_combined.ash")
    );
    assert!(
        causes[1]["path"]
            .as_str()
            .unwrap()
            .ends_with("combined_forms.ash")
    );
    assert_eq!(causes[0]["byte_start"], causes[2]["byte_start"]);
    assert_eq!(causes[0]["byte_end"], causes[2]["byte_end"]);
    let frames: Vec<_> = labels
        .iter()
        .filter(|label| label["relationship"] == "syntax_definition")
        .collect();
    assert_eq!(frames.len(), 1, "{json}");
    assert!(
        frames[0]["path"]
            .as_str()
            .unwrap()
            .ends_with("combined_forms.ash")
    );
}

#[test]
fn captured_failures_before_completion_preserve_invocation() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    for (entry, reason) in [
        ("captured_missing.ash", "resolve.unknown-name"),
        ("captured_function.ash", "type.function-needs-context"),
    ] {
        let failure = compile_path(fixture(&format!("template-diagnostic/{entry}")))
            .expect_err("the captured expression fails in the ordinary pipeline");
        assert_eq!(failure.reason_code(), reason);
        let diagnostics = compile_file_diagnostics(&failure).unwrap();
        let mut json = Vec::new();
        write_json(&mut json, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
        let labels = json["labels"].as_array().unwrap();
        assert!(
            labels.iter().any(|label| {
                label["relationship"] == "syntax_invocation"
                    && label["path"].as_str().unwrap().ends_with(entry)
            }),
            "{entry}: {json}"
        );
        assert!(
            labels.iter().any(|label| {
                label["relationship"] == "syntax_definition"
                    && label["path"].as_str().unwrap().ends_with("forms.ash")
            }),
            "{entry}: {json}"
        );
    }
}

#[test]
fn nested_expansions_keep_distinct_frames_with_equal_invocation_spans() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    let failure = compile_path(fixture("template-diagnostic/nested_invalid.ash"))
        .expect_err("the inner syntax produces a Bool operand");
    assert_eq!(failure.reason_code(), "type.operator-operand");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    let frames = labels
        .iter()
        .filter(|label| {
            matches!(
                label["relationship"].as_str(),
                Some("syntax_invocation" | "syntax_definition")
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(frames.len(), 4, "{json}");
    assert_eq!(frames[0]["relationship"], "syntax_invocation");
    assert_eq!(frames[1]["relationship"], "syntax_definition");
    assert!(
        frames[1]["path"]
            .as_str()
            .unwrap()
            .ends_with("nested_forms.ash")
    );
    assert_eq!(frames[2]["relationship"], "syntax_invocation");
    assert_eq!(frames[0]["path"], frames[2]["path"]);
    assert_eq!(frames[0]["byte_start"], frames[2]["byte_start"]);
    assert_eq!(frames[0]["byte_end"], frames[2]["byte_end"]);
    assert_eq!(frames[3]["relationship"], "syntax_definition");
    assert!(frames[3]["path"].as_str().unwrap().ends_with("/forms.ash"));
}

#[test]
fn generated_diagnostic_preserves_combined_causes_without_repeating_its_frame() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    let failure = compile_path(fixture("template-diagnostic/combined_invalid.ash"))
        .expect_err("the generated Bool is not an Int");
    assert_eq!(failure.reason_code(), "type.operator-operand");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    let causes = labels
        .iter()
        .filter(|label| label["relationship"] == "syntax_cause")
        .collect::<Vec<_>>();
    assert_eq!(causes.len(), 2, "{json}");
    assert!(
        causes[0]["path"]
            .as_str()
            .unwrap()
            .ends_with("combined_forms.ash")
    );
    assert!(
        causes[1]["path"]
            .as_str()
            .unwrap()
            .ends_with("combined_invalid.ash")
    );
    assert_eq!(
        labels
            .iter()
            .filter(|label| label["relationship"] == "syntax_invocation")
            .count(),
        1,
        "{json}"
    );
    assert_eq!(
        labels
            .iter()
            .filter(|label| label["relationship"] == "syntax_definition")
            .count(),
        1,
        "{json}"
    );
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
fn template_names_are_checked_when_expanded() {
    use ash::presentation::{compile_file_diagnostics, write_json};

    for path in [
        "template-admission/missing/entry.ash",
        "template-admission/missing_nested/entry.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect("unused names need no lookup");
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    let failure = compile_path(fixture("template-admission/missing/invoked.ash"))
        .expect_err("expansion cannot resolve a missing helper through the caller");
    assert_eq!(failure.reason_code(), "resolve.unknown-name");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    let forms = include_str!("fixtures/surface-macros/template-admission/missing/forms.ash");
    let missing = forms.find("missing $value").unwrap();
    assert_eq!(labels[0]["relationship"], "unresolved_name");
    assert!(labels[0]["path"].as_str().unwrap().ends_with("forms.ash"));
    assert_eq!(labels[0]["byte_start"], missing);
    assert_eq!(labels[0]["byte_end"], missing + "missing".len());
    assert!(
        !labels
            .iter()
            .any(|label| label["relationship"] == "syntax_cause")
    );
    assert_eq!(labels.len(), 3, "{json}");
    assert_eq!(labels[1]["relationship"], "syntax_invocation");
    assert_eq!(labels[2]["relationship"], "syntax_definition");
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
    let unused = compile_path(fixture("template-annotation/captured/applied_missing.ash"))
        .expect("an unused template does not resolve the missing type");
    assert_eq!(execute(&unused).unwrap().value_display(), "42");
    let path = "template-annotation/captured/applied_wrong.ash";
    let failure = compile_path(fixture(path)).expect_err(path);
    assert_eq!(
        failure.reason_code(),
        "type.binding-initializer",
        "{path}: {failure:?}"
    );
}

#[test]
fn template_captured_identifier_selects_a_caller_effect() {
    for path in [
        "template-perform/captured/entry.ash",
        "template-perform/captured/generic.ash",
        "template-perform/captured/missing_operand.ash",
        "template-perform/captured/missing_argument.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, expected) in [
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
        "template-perform/captured/operation_missing_operand.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    let path = "template-perform/captured/operation_unknown.ash";
    let failure = compile_path(fixture(path)).expect_err(path);
    assert_eq!(
        failure.reason_code(),
        "resolve.unknown-name",
        "{path}: {failure:?}"
    );
    let failure = compile_path(fixture("template-perform/captured/private_direct.ash"))
        .expect_err("the syntax import does not expose its owner's private effect");
    assert_eq!(failure.reason_code(), "effect.unknown");
}

#[test]
fn template_captured_identifier_selects_a_handler_effect_or_operation() {
    for path in [
        "template-handler-capture/entry.ash",
        "template-handler-capture/operation.ash",
        "template-handler-capture/missing_body.ash",
        "template-handler-capture/missing_handled.ash",
        "template-handler-capture/missing_store.ash",
        "template-handler-capture/missing_argument.ash",
        "template-handler-capture/missing_operation.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    let path = "template-handler-capture/operation_unknown.ash";
    let failure = compile_path(fixture(path)).expect_err(path);
    assert_eq!(
        failure.reason_code(),
        "resolve.unknown-name",
        "{path}: {failure:?}"
    );
}

#[test]
fn template_captured_identifier_selects_an_effect_row_member() {
    for path in [
        "template-row-capture/entry.ash",
        "template-row-capture/manual.ash",
        "template-row-capture/local_evidence_unused.ash",
        "template-row-capture/missing_argument.ash",
        "template-row-capture/missing_literal.ash",
    ] {
        let compiled = compile_path(fixture(path)).expect(path);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42", "{path}");
    }
    for (path, reason) in [
        (
            "template-row-capture/invoked_missing_literal.ash",
            "effect.unknown",
        ),
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
        "template-private-evidence/local_shadow.ash",
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
