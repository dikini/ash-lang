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
