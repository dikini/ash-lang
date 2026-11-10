use std::{path::PathBuf, process::Command};

fn run(entry: &str, json: bool) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("docs/design/macros/fixtures/diagnostics")
        .join(entry);
    let mut command = Command::new(env!("CARGO_BIN_EXE_ash"));
    command.args(["--locale", "en"]);
    if json {
        command.args(["--message-format", "json"]);
    }
    let output = command.arg(path).output().expect("driver starts");
    assert_eq!(output.status.code(), Some(1));
    String::from_utf8(output.stderr).unwrap()
}

fn label<'a>(json: &'a serde_json::Value, relationship: &str) -> &'a serde_json::Value {
    let labels = json["labels"].as_array().unwrap();
    let matching: Vec<_> = labels
        .iter()
        .filter(|label| label["relationship"] == relationship)
        .collect();
    assert_eq!(matching.len(), 1, "{json}");
    matching[0]
}

fn assert_span(label: &serde_json::Value, path: &str, start: usize, end: usize) {
    assert!(label["path"].as_str().unwrap().ends_with(path), "{label}");
    assert_eq!(label["byte_start"], start, "{label}");
    assert_eq!(label["byte_end"], end, "{label}");
}

#[test]
fn fixed_i15_missing_identifier_reports_matcher_origins() {
    let human = run("missing.ash", false);
    assert!(human.contains("An identifier is required here."), "{human}");
    assert!(human.contains("missing.ash"), "{human}");
    assert!(human.contains("typed_forms.ash"), "{human}");
    assert!(human.contains("The syntax was invoked here"), "{human}");
    assert!(human.contains("The syntax was defined here"), "{human}");

    let json: serde_json::Value = serde_json::from_str(&run("missing.ash", true)).unwrap();
    assert_eq!(json["reason"], "parse.expected-form");
    assert!(
        json["facts"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fact| fact["name"] == "expected" && fact["value"] == "identifier"),
        "{json}"
    );
    assert!(
        json["facts"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fact| fact["name"] == "found" && fact["value"] == "line-end"),
        "{json}"
    );
    assert_span(&json["labels"][0], "missing.ash", 48, 49);
    assert_eq!(json["labels"][0]["relationship"], "expected_form");
    assert_span(label(&json, "syntax_invocation"), "missing.ash", 39, 48);
    assert_span(
        label(&json, "syntax_definition"),
        "typed_forms.ash",
        103,
        203,
    );
}

#[test]
fn fixed_i14_category_reports_retained_matcher_origins() {
    let human = run("category.ash", false);
    assert!(
        human.contains("This token is not allowed at this grammar position."),
        "{human}"
    );
    assert!(human.contains("category.ash"), "{human}");
    assert!(human.contains("category_forms.ash"), "{human}");
    assert!(human.contains("The syntax was invoked here"), "{human}");
    assert!(human.contains("The syntax was defined here"), "{human}");

    let json: serde_json::Value = serde_json::from_str(&run("category.ash", true)).unwrap();
    assert_eq!(json["reason"], "parse.unexpected-token");
    assert!(
        json["facts"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fact| fact["name"] == "found" && fact["value"] == "Int"),
        "{json}"
    );
    assert_span(&json["labels"][0], "category.ash", 45, 63);
    assert_span(label(&json, "syntax_invocation"), "category.ash", 45, 63);
    assert_span(
        label(&json, "syntax_definition"),
        "category_forms.ash",
        43,
        109,
    );
}
