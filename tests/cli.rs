use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempFile(PathBuf);

impl TempFile {
    fn write(bytes: &[u8]) -> Self {
        let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!("ash-cli-{}-{id}.ash", std::process::id()));
        fs::write(&path, bytes).expect("test input should be writable");
        Self(path)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
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
    let fixture = Path::new("tests/fixtures/first-stratum/valid/v001-precedence.ash");
    let output = ash(&[fixture]);

    assert!(output.status.success());
    assert_eq!(output.stdout, b"7 : Int\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn invocation_requires_exactly_one_source_path() {
    let none = ash(&[]);
    assert_eq!(none.status.code(), Some(2));
    assert!(none.stdout.is_empty());
    assert!(!none.stderr.is_empty());

    let first = TempFile::write(b"1\n");
    let second = TempFile::write(b"2\n");
    let many = ash(&[first.path(), second.path()]);
    assert_eq!(many.status.code(), Some(2));
    assert!(many.stdout.is_empty());
    assert!(!many.stderr.is_empty());
}

#[test]
fn missing_and_invalid_utf8_inputs_are_invocation_failures() {
    let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
    let missing =
        std::env::temp_dir().join(format!("ash-cli-missing-{}-{id}.ash", std::process::id()));
    let missing_output = ash(&[&missing]);
    assert_eq!(missing_output.status.code(), Some(2));
    assert!(missing_output.stdout.is_empty());
    assert!(!missing_output.stderr.is_empty());

    let invalid_utf8 = TempFile::write(&[0xff, 0xfe]);
    let invalid_output = ash(&[invalid_utf8.path()]);
    assert_eq!(invalid_output.status.code(), Some(2));
    assert!(invalid_output.stdout.is_empty());
    assert!(!invalid_output.stderr.is_empty());
}

#[test]
fn rejected_ash_source_uses_status_one_without_success_output() {
    let source = TempFile::write(b"true + 1\n");
    let output = ash(&[source.path()]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).expect("diagnostics should be UTF-8");
    assert!(stderr.contains("type.operator-operand"));
    assert!(stderr.contains("expected Int"));
    assert!(stderr.contains("found Bool"));
}
