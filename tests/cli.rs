use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{RunConfiguration, run_path},
    eval::Value,
    module::ModuleRoots,
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

#[test]
fn explicit_diagnostic_formats_reach_source_reporting_and_preserve_exit_status() {
    let entry = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/first-stratum/type/binding-initializer.ash");
    for format in ["human", "short", "json"] {
        let output = Command::new(env!("CARGO_BIN_EXE_ash"))
            .args(["--message-format", format, "--locale", "bg"])
            .arg(&entry)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        if format == "json" {
            let json: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
            assert_eq!(json["reason"], "type.binding-initializer");
            assert_eq!(json["responsibility"], "source");
            assert!(!json["labels"].as_array().unwrap().is_empty());
        } else {
            let text = String::from_utf8(output.stderr).unwrap();
            assert!(text.contains("Тази променлива изисква"));
            assert!(text.contains("type.binding-initializer"));
        }
    }
}

#[test]
fn explicit_json_usage_errors_honor_format_despite_earlier_invalid_arguments() {
    for args in [
        vec!["--bad", "--message-format", "json", "entry.ash"],
        vec!["--message-format", "json", "--bad", "entry.ash"],
        vec!["--locale", "--message-format", "json", "entry.ash"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_ash"))
            .args(args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        let json: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
        assert_eq!(json["reason"], "invocation.usage");
    }
}

#[test]
fn explicit_options_preserve_success_stdout_and_select_input_json() {
    let entry = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/first-stratum/valid/v001-precedence.ash");
    let original = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(&entry)
        .output()
        .unwrap();
    let selected = Command::new(env!("CARGO_BIN_EXE_ash"))
        .args(["--message-format", "json"])
        .arg(&entry)
        .output()
        .unwrap();
    assert_eq!(selected.status.code(), Some(0));
    assert_eq!(selected.stdout, original.stdout);
    assert!(selected.stderr.is_empty());
    let missing = TempDirectory::create().0.join("missing.ash");
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .args(["--message-format", "json"])
        .arg(missing)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    let json: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
    assert_eq!(json["reason"], "input.read");
}

struct TempDirectory(PathBuf);

impl TempDirectory {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!("ash-cli-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("test directory should be creatable: {error}"),
            }
        }
    }
}

impl Drop for TempDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir(&self.0);
    }
}

struct TempFile {
    _directory: TempDirectory,
    path: PathBuf,
}

impl TempFile {
    fn write(bytes: &[u8]) -> Self {
        let directory = TempDirectory::create();
        let path = directory.0.join("source.ash");
        fs::write(&path, bytes).expect("test input should be writable");
        Self {
            _directory: directory,
            path,
        }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn ash(arguments: &[&Path]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ash"))
        .args(arguments)
        .output()
        .expect("the Ash executable should start")
}

#[test]
fn v001_fixture_prints_exactly_one_value_and_type_line() {
    let source = TempFile::write(include_bytes!(
        "fixtures/first-stratum/valid/v001-precedence.ash"
    ));
    let output = ash(&[source.path()]);

    assert!(output.status.success());
    assert_eq!(output.stdout, b"7 : Int\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn false_literal_has_exact_library_and_cli_observations() {
    let source = TempFile::write(b"main : Unit -> Bool\nmain () = false\n");
    let observation = run_path(RunConfiguration {
        entry: source.path().to_path_buf(),
        roots: ModuleRoots::empty(),
    })
    .expect("false should run end to end");
    assert!(matches!(observation.value(), Value::Boolean(false)));
    assert_eq!(observation.ty(), &Type::Bool);

    let output = ash(&[source.path()]);
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"false : Bool\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn handled_effect_prints_the_resumed_value_and_pure_entry_type() {
    let source = TempFile::write(
        concat!(
            "effect Ask {\nask : Int -> Int\n}\n\n",
            "main : Unit -> Int\n",
            "main () = handle (perform Ask.ask 1) with Ask {\n",
            "ask value => resume (value + 41)\n}\n",
        )
        .as_bytes(),
    );
    let output = ash(&[source.path()]);
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : Int\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn invocation_requires_exactly_one_source_path() {
    let none = ash(&[]);
    assert_eq!(none.status.code(), Some(2));
    assert!(none.stdout.is_empty());
    assert_eq!(
        none.stderr,
        b"usage: ash [--root name=path]... <entry-file>\n"
    );

    let first = TempFile::write(b"main : Unit -> Int\nmain () = 1\n");
    let second = TempFile::write(b"main : Unit -> Int\nmain () = 2\n");
    let many = ash(&[first.path(), second.path()]);
    assert_eq!(many.status.code(), Some(2));
    assert!(many.stdout.is_empty());
    assert_eq!(
        many.stderr,
        b"usage: ash [--root name=path]... <entry-file>\n"
    );
}

#[test]
fn missing_and_invalid_utf8_inputs_are_invocation_failures() {
    let missing_directory = TempDirectory::create();
    let missing = missing_directory.0.join("missing.ash");
    let missing_output = ash(&[&missing]);
    assert_eq!(missing_output.status.code(), Some(2));
    assert!(missing_output.stdout.is_empty());
    assert!(missing_output.stderr.starts_with(b"input.read\n"));

    let invalid_utf8 = TempFile::write(&[0xff, 0xfe]);
    let invalid_output = ash(&[invalid_utf8.path()]);
    assert_eq!(invalid_output.status.code(), Some(2));
    assert!(invalid_output.stdout.is_empty());
    assert!(invalid_output.stderr.starts_with(b"input.invalid-utf8\n"));
}

#[test]
fn excluded_bare_carriage_return_is_a_source_rejection() {
    let bare_cr = TempFile::write(b"main : Unit -> Int\nmain () = 1\r2");
    let output = ash(&[bare_cr.path()]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.starts_with(b"lex.bare-carriage-return\n"));
}

#[test]
fn rejected_ash_source_uses_status_one_without_success_output() {
    let source = TempFile::write(b"main : Unit -> Int\nmain () = true + 1\n");
    let output = ash(&[source.path()]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).expect("diagnostics should be UTF-8");
    assert!(stderr.contains("type.operator-operand"));
    assert!(stderr.contains("expected Int"));
    assert!(stderr.contains("found Bool"));
}

#[test]
fn recursive_source_rejections_use_stable_cli_categories() {
    for (text, category) in [
        (
            b"main : Unit -> Int\nmain () = {\nlet rec value : Int = 1\nand\nvalue\n}\n"
                .as_slice(),
            "parse.expected-recursive-member",
        ),
        (
            b"main : Unit -> Int\nmain () = {\nand stray : Int = 1\n42\n}\n".as_slice(),
            "parse.unexpected-and",
        ),
        (
            b"main : Unit -> Int\nmain () = {\nlet rec same : Unit -> Int = fn(value) {\n1\n}\nand same : Unit -> Int = fn(value) {\n2\n}\nsame ()\n}\n".as_slice(),
            "resolve.duplicate-recursive-member",
        ),
        (
            b"main : Unit -> Int\nmain () = {\nlet rec value : Int = 1\nvalue\n}\n"
                .as_slice(),
            "recursion.unsafe-root",
        ),
    ] {
        let source = TempFile::write(text);
        let output = ash(&[source.path()]);
        assert_eq!(output.status.code(), Some(1), "category: {category}");
        assert!(output.stdout.is_empty(), "category: {category}");
        let stderr = String::from_utf8(output.stderr).expect("diagnostics should be UTF-8");
        assert!(
            stderr.starts_with(&format!("{category}\n")),
            "unexpected stderr for {category}: {stderr:?}"
        );
    }
}

fn assert_source_failure(source: &[u8], category: &str, labels: &[&str]) {
    let source = TempFile::write(source);
    let output = ash(&[source.path()]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).expect("diagnostics should be UTF-8");
    assert!(stderr.contains(category), "missing category in {stderr:?}");
    for label in labels {
        assert!(
            stderr.contains(label),
            "missing label {label:?} in {stderr:?}"
        );
    }
}

#[test]
fn parse_failure_reports_the_primary_and_recovery_labels() {
    assert_source_failure(
        include_bytes!("fixtures/first-stratum/parse/p003-independent-recovery.ash"),
        "parse.expected-operand",
        &[
            "the operator requires a right operand",
            "parsing resumes at this block closing brace",
            "parse.unclosed-group",
            "the opening parenthesis is not closed",
        ],
    );
}

#[test]
fn resolution_failure_reports_both_duplicate_definitions() {
    assert_source_failure(
        include_bytes!("fixtures/first-stratum/resolve/r002-duplicate-global.ash"),
        "resolve.duplicate-global",
        &[
            "this global name is already defined",
            "the first global name is here",
            "the first complete definition is here",
        ],
    );
}

#[test]
fn type_failure_reports_the_argument_and_declared_domain() {
    assert_source_failure(
        include_bytes!("fixtures/first-stratum/type/t004-argument.ash"),
        "type.argument",
        &[
            "this argument does not match the function domain",
            "the function domain is required here",
            "expected Int",
            "found Bool",
        ],
    );
}

#[test]
fn kind_failure_reports_the_causal_occurrence_and_declared_constructor() {
    assert_source_failure(
        b"type Option<A> =\nNone\n| Some(A)\n\nbad : Option -> Int\nbad _ = 0\n",
        "kind.expected-type",
        &[
            "this function domain must have kind Type",
            "the found kind is fixed by this declaration",
            "expected Type",
            "found Type -> Type",
        ],
    );
}

#[test]
fn annotated_binding_failure_reports_the_initializer_and_annotation() {
    assert_source_failure(
        include_bytes!("fixtures/first-stratum/type/binding-initializer.ash"),
        "type.binding-initializer",
        &[
            "this initializer has type Int",
            "this binding annotation requires Bool",
            "expected Bool",
            "found Int",
        ],
    );
}
