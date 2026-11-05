use std::path::PathBuf;

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    lexer::lex,
    module::ModuleRoots,
    parser::{parse, project_module},
    source::SourceFile,
};

#[test]
fn frozen_transformer_body_parses_as_ordinary_ash() {
    let fixture = include_str!("fixtures/surface-macros/macros.ash");
    let start = fixture
        .find("expand_twice :")
        .expect("transformer signature");
    let source = SourceFile::new("transformer.ash", fixture[start..].to_owned()).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(tree.lexical_diagnostics().is_empty(), "{tree:?}");
    assert!(tree.parse_diagnostics().is_empty(), "{tree:?}");
    project_module(&source, &tree).expect("ordinary transformer projects");
}

#[test]
fn checked_ash_transformer_constructs_expression_from_capture() {
    let configuration = RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/surface-macros/entry_host.ash"),
        roots: ModuleRoots::empty(),
    };
    let compiled = compile_path(configuration).expect("macro host graph compiles");
    let actual = execute(&compiled).expect("macro host graph executes");
    assert_eq!(actual.value_display(), "42");
    assert_eq!(actual.type_display(), "Int");
}

#[test]
fn compiler_syntax_module_loads_through_the_driver() {
    let configuration = RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/surface-macros/compiler-syntax-import.ash"),
        roots: ModuleRoots::empty(),
    };
    let compiled = compile_path(configuration).expect("compiler syntax module loads and checks");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

fn macro_fixture(name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/surface-macros")
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

#[test]
fn template_can_invoke_an_imported_transformer_from_another_source() {
    let compiled = compile_path(macro_fixture("entry_procedural_wrapper.ash"))
        .expect("template-invoked transformer compiles");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn unused_transformer_rejects_a_missing_local_target() {
    let failure = compile_path(macro_fixture("invalid_transformer_missing.ash")).unwrap_err();
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert_eq!(failure.reason_code(), "syntax.invalid-transformer");
}

#[test]
fn unused_transformer_rejects_a_wrong_type() {
    let failure = compile_path(macro_fixture("invalid_transformer_type.ash")).unwrap_err();
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert_eq!(failure.reason_code(), "syntax.invalid-transformer");
}

#[test]
fn unused_private_transformer_is_checked_without_being_run() {
    let compiled = compile_path(macro_fixture("unused_private_transformer.ash"))
        .expect("an unused valid private transformer is admitted without running it");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn unused_transformer_rejects_other_effects() {
    let failure = compile_path(macro_fixture("invalid_transformer_effect.ash")).unwrap_err();
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert_eq!(failure.reason_code(), "syntax.invalid-transformer");
}

#[test]
fn checked_transformers_inspect_and_construct_lexical_tokens() {
    let compiled = compile_path(macro_fixture("entry_token_ops.ash"))
        .expect("transformers can construct and inspect ordinary tokens");
    assert_eq!(execute(&compiled).unwrap().value_display(), "78");
}

#[test]
fn checked_transformer_emits_structured_parentheses() {
    let compiled = compile_path(macro_fixture("entry_group_output.ash"))
        .expect("transformer can emit a structured parenthesis group");
    assert_eq!(execute(&compiled).unwrap().value_display(), "32");
}

#[test]
fn checked_transformer_emits_structured_braces_and_logical_lines() {
    let compiled = compile_path(macro_fixture("entry_brace_output.ash"))
        .expect("transformer can emit a structured block group");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn checked_transformer_preserves_a_captured_identifier_context() {
    let compiled = compile_path(macro_fixture("entry_identifier_ops.ash"))
        .expect("transformer can inspect and return the captured identifier");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn checked_transformer_uses_a_captured_identifier_as_a_binder() {
    let compiled = compile_path(macro_fixture("entry_binder_ops.ash"))
        .expect("transformer can emit the captured binder and body");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn checked_transformer_fresh_identifier_does_not_capture_the_caller() {
    let compiled = compile_path(macro_fixture("entry_constructed_fresh.ash"))
        .expect("a fresh identifier binds only its own references");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn checked_transformer_caller_identifier_can_bind_caller_syntax() {
    let compiled = compile_path(macro_fixture("entry_constructed_caller.ash"))
        .expect("a caller-context binder captures the caller expression");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn checked_transformer_definition_identifier_uses_its_private_helper() {
    let compiled = compile_path(macro_fixture("entry_constructed_private.ash"))
        .expect("a definition-context name retains its owner under caller shadowing");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn checked_transformer_parses_without_resolving_and_reuses_a_fragment() {
    let compiled = compile_path(macro_fixture("entry_parse_ops.ash"))
        .expect("transformer can parse structured syntax without resolving it");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn expression_unwrapping_preserves_groups_and_nested_fragments() {
    for (fixture, expected) in [
        ("entry_unwrap_plain.ash", "21"),
        ("entry_unwrap_protected.ash", "30"),
        ("entry_unwrap_reparsed.ash", "30"),
        ("entry_unwrap_grouped.ash", "30"),
        ("entry_unwrap_forwarded.ash", "21"),
        ("entry_unwrap_forwarded_grouped.ash", "30"),
    ] {
        let compiled = compile_path(macro_fixture(fixture)).expect(fixture);
        assert_eq!(
            execute(&compiled).unwrap().value_display(),
            expected,
            "{fixture}"
        );
    }
}

#[test]
fn generated_nested_unwrap_keeps_the_protected_fragment() {
    let compiled = compile_path(macro_fixture("entry_unwrap_generated_protected.ash"))
        .expect("a generated nested invocation keeps its protected argument");
    assert_eq!(execute(&compiled).unwrap().value_display(), "30");
}

#[test]
fn generated_definition_context_recognizes_nested_syntax() {
    let compiled = compile_path(macro_fixture("entry_generated_nested.ash"))
        .expect("generated name selects syntax imported by its definition owner");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn generated_caller_context_selects_the_callers_syntax() {
    let compiled = compile_path(macro_fixture("entry_generated_caller.ash"))
        .expect("caller-context name selects the caller's syntax");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

#[test]
fn generated_fresh_context_does_not_select_syntax_or_caller_binding() {
    let failure = compile_path(macro_fixture("entry_generated_fresh.ash")).unwrap_err();
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert_eq!(failure.reason_code(), "resolve.unknown-name");
}

#[test]
fn parse_expression_does_not_run_discarded_nested_syntax() {
    let compiled = compile_path(macro_fixture("entry_generated_parse_discard.ash"))
        .expect("parsing a nested syntax invocation does not execute its transformer");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}
