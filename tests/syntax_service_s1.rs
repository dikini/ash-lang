use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
};

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};

fn fixture(directory: &str, name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures")
            .join(directory)
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

struct SourceTree(PathBuf);

impl SourceTree {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-syntax-service-s1-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, text: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, text).unwrap();
        path
    }

    fn configuration(&self, entry: &Path) -> RunConfiguration {
        RunConfiguration {
            entry: entry.to_owned(),
            roots: ModuleRoots::empty(),
        }
    }
}

impl Drop for SourceTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn old_exhaustive_capture_match_rejects_extended_sum() {
    let failure = compile_path(fixture("migration", "old.ash"))
        .expect_err("the old capture match omits new cases");
    assert_eq!(failure.reason_code(), "coverage.non-exhaustive");
}

#[test]
fn migrated_and_fallback_capture_matches_preserve_expression_behavior() {
    for name in ["new.ash", "fallback.ash"] {
        let compiled = compile_path(fixture("migration", name)).expect(name);
        let result = execute(&compiled).unwrap();
        assert_eq!(result.value_display(), "42", "{name}");
        assert_eq!(result.type_display(), "Int", "{name}");
    }
}

#[test]
fn old_exhaustive_token_match_rejects_extended_sum() {
    let failure = compile_path(fixture("escapes", "token_exhaustive.ash"))
        .expect_err("the old token match omits the two new cases");
    assert_eq!(failure.reason_code(), "coverage.non-exhaustive");
}

#[test]
fn fixed_token_kinds_transformer_checks_exact_spelling_through_the_driver() {
    let tree = SourceTree::new();
    tree.write(
        "identity_forms.ash",
        include_str!("../docs/design/macros/fixtures/escapes/identity_forms.ash"),
    );
    let entry = tree.write(
        "main.ash",
        "import identity_forms (syntax token_kinds)\nmain : Unit -> Int\nmain () = token_kinds 42\n",
    );
    let compiled = compile_path(tree.configuration(&entry)).expect("token transformer checks");
    let result = execute(&compiled).unwrap();
    assert_eq!(result.value_display(), "42");
    assert_eq!(result.type_display(), "Int");
}

#[test]
fn public_fragment_sums_and_nested_repeated_capture_are_closed() {
    let tree = SourceTree::new();
    let entry = tree.write(
        "main.ash",
        r#"import @builtin.compiler.syntax as Syntax

unwrap_declaration : Syntax.DeclarationFragment -> Syntax.Syntax ! {Syntax.Ops}
unwrap_declaration item = Syntax.declaration_syntax(item)

node_kind : Syntax.Node -> Int
node_kind (Syntax.TokenNode(_, _)) = 0
node_kind (Syntax.IdentifierNode(_, _)) = 0
node_kind (Syntax.GroupNode(_, _, _)) = 0
node_kind (Syntax.ExpressionNode(_, _)) = 0
node_kind (Syntax.TypeNode(_, _)) = 0
node_kind (Syntax.PatternNode(_, _)) = 0
node_kind (Syntax.DeclarationNode(_, _)) = 0

result_kind : Syntax.ParseResult -> Int
result_kind (Syntax.Parsed(_)) = 0
result_kind (Syntax.ParseRejected(_)) = 0
result_kind (Syntax.ParsedType(_)) = 0
result_kind (Syntax.ParsedPattern(_)) = 0
result_kind (Syntax.ParsedDeclaration(_)) = 0

classify : Syntax.Capture -> Int
classify (Syntax.RepeatedCapture(Syntax.MoreCaptures(Syntax.RepeatedCapture(Syntax.NoCaptures), Syntax.NoCaptures))) = 42
classify _ = 0

fallback : Syntax.Capture -> Int
fallback (Syntax.ExpressionCapture(_)) = 1
fallback _ = 0

main : Unit -> Int
main () = classify(Syntax.RepeatedCapture(Syntax.MoreCaptures(Syntax.RepeatedCapture(Syntax.NoCaptures), Syntax.NoCaptures))) + fallback(Syntax.RepeatedCapture(Syntax.NoCaptures))
"#,
    );
    let compiled = compile_path(tree.configuration(&entry)).expect("extended sums check");
    assert_eq!(execute(&compiled).unwrap().value_display(), "42");
}

fn declaration_service_fixture(name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/surface-macros/declaration-service")
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

fn declaration_service_runs(name: &str) {
    let compiled = compile_path(declaration_service_fixture(name))
        .unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
    let result = execute(&compiled).unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
    assert_eq!(result.value_display(), "42", "{name}");
    assert_eq!(result.type_display(), "Int", "{name}");
}

#[test]
fn declaration_parse_returns_authentic_declarations_and_handles_rejection() {
    for name in ["parse/plain.ash", "parse/node.ash", "parse/handled.ash"] {
        declaration_service_runs(name);
    }
}

#[test]
fn declaration_parse_does_not_resolve_check_or_expand_discarded_syntax() {
    for name in [
        "parse/unresolved.ash",
        "parse/type-invalid.ash",
        "parse/no-expansion.ash",
        "parse/quoted-inspect.ash",
    ] {
        declaration_service_runs(name);
    }
}

#[test]
fn declaration_parse_rejects_empty_and_multiple_declarations() {
    use ash::{
        driver::PipelineFailure,
        presentation::{compile_file_diagnostics, write_json},
    };

    for (entry, found) in [("empty.ash", "end-of-file"), ("two.ash", "identifier")] {
        let name = format!("parse/{entry}");
        let failure = compile_path(declaration_service_fixture(&name))
            .expect_err("parse_declaration rejects this input");
        assert!(failure.is_source_rejection(), "{name}: {failure:?}");
        assert!(
            matches!(
                failure.pipeline_failure(),
                Some(PipelineFailure::SyntaxParse(_))
            ),
            "{name}: {failure:?}"
        );
        assert_eq!(failure.reason_code(), "parse.unexpected-token", "{name}");
        let diagnostics = compile_file_diagnostics(&failure).expect("parser diagnostic");
        let [diagnostic] = diagnostics.as_slice() else {
            panic!("{name}: expected one diagnostic, got {}", diagnostics.len())
        };
        let mut json = Vec::new();
        write_json(&mut json, diagnostic).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
        assert_eq!(json["reason"], "parse.unexpected-token", "{name}: {json}");
        assert!(
            json["facts"]
                .as_array()
                .unwrap()
                .iter()
                .any(|fact| { fact["name"] == "found" && fact["value"] == found }),
            "{name}: {json}"
        );
        let labels = json["labels"].as_array().expect("source labels");
        for (relationship, path) in [
            ("syntax_invocation", name.as_str()),
            ("syntax_definition", "parse/forms.ash"),
        ] {
            assert!(
                labels.iter().any(|label| {
                    label["relationship"] == relationship
                        && label["path"]
                            .as_str()
                            .is_some_and(|path_text| Path::new(path_text).ends_with(path))
                }),
                "{name}: {json}"
            );
        }
    }
}

#[test]
fn repeated_captures_preserve_nested_order_and_protected_leaf_consumers() {
    for name in [
        "repeated/nested.ash",
        "repeated/declaration.ash",
        "mixed/main.ash",
    ] {
        declaration_service_runs(name);
    }
}

#[test]
fn protected_fragments_survive_parsed_declaration_output() {
    for name in ["protected-control/main.ash", "protected/main.ash"] {
        declaration_service_runs(name);
    }
}

#[test]
fn quoted_declaration_survives_parsed_declaration_output() {
    for name in ["quote/source_control.ash", "quote/emitted.ash"] {
        declaration_service_runs(name);
    }
}
