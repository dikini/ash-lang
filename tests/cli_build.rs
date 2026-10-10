use std::{path::Path, process::Command};

#[test]
fn build_invocation_preserves_source_diagnostics_without_linking() {
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .args([
            "build",
            "--message-format",
            "json",
            "--output",
            "unused-program",
            "/nonexistent/ash-build-entry.ash",
        ])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let diagnostic: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
    assert_eq!(diagnostic["reason"], "input.read");
}

#[test]
fn build_invocation_reports_preparation_refusal_in_the_selected_format() {
    let entry = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/first-stratum/valid/v001-precedence.ash");
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .args([
            "--message-format",
            "json",
            "build",
            "--output",
            "unused-program",
            "--target",
            "unsupported-profile",
        ])
        .arg(entry)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let diagnostic: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
    assert_eq!(diagnostic["reason"], "build.unsupported-target");
    assert_eq!(diagnostic["responsibility"], "invocation");
}

#[test]
fn build_invocation_requires_one_output_and_options_before_the_entry() {
    for arguments in [
        vec!["build", "entry.ash"],
        vec!["build", "--output", "one", "--output", "two", "entry.ash"],
        vec!["build", "entry.ash", "--output", "program"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_ash"))
            .args(["--message-format", "json"])
            .args(arguments)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        let diagnostic: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
        assert_eq!(diagnostic["reason"], "invocation.usage");
    }
}
