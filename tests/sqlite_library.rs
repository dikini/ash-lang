//! Connected workloads import the product Ash copying SQLite library.

use ash::{
    build::{BuildConfiguration, NativeLinkInput, build_prepared, prepare_program},
    driver::{RunConfiguration, compile_path, run_path},
    module::ModuleRoots,
};
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::Read,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir().join(format!(
            "ash-sqlite-library-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        Self(root)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn imported_product_sqlite_selects_42_with_nested_completion() {
    product_probe(
        "Sqlite.Result<Int>",
        r#"match Sqlite.step statement {
            Sqlite.Row => Sqlite.column_int (statement, 0)
            Sqlite.Done => Sqlite.Err Sqlite.MissingRow
            Sqlite.StepError(error) => Sqlite.Err error
        }"#,
        "SELECT 42",
        "Completed(Completed(Ok(42), Closed), Closed)",
    );
}

#[test]
fn imported_product_sqlite_rejects_non_whitespace_tail() {
    product_probe(
        "Int",
        "42",
        "SELECT 42; SELECT 43",
        "Completed(NotAcquired(InvalidTail), Closed)",
    );
}

#[test]
fn imported_product_sqlite_checks_bind_reset_and_clear_protocol_methods() {
    product_probe(
        "(Sqlite.Result<Unit>, Sqlite.Result<Int>, Sqlite.StepResult, Sqlite.Result<Unit>, Sqlite.Result<Unit>, Sqlite.Result<Int>)",
        r#"let bound = Sqlite.bind_int (statement, 1, 42)
        let first = match Sqlite.step statement {
            Sqlite.Row => Sqlite.column_int (statement, 0)
            Sqlite.Done => Sqlite.Err Sqlite.MissingRow
            Sqlite.StepError(error) => Sqlite.Err error
        }
        let done = Sqlite.step statement
        let refused = Sqlite.bind_int (statement, 1, 99)
        let reset = Sqlite.reset statement
        let _ = Sqlite.clear_bindings statement
        let _ = Sqlite.bind_int (statement, 1, 99)
        let second = match Sqlite.step statement {
            Sqlite.Row => Sqlite.column_int (statement, 0)
            Sqlite.Done => Sqlite.Err Sqlite.MissingRow
            Sqlite.StepError(error) => Sqlite.Err error
        }
        (bound, first, done, refused, reset, second)"#,
        "SELECT ?1",
        "Completed(Completed((Ok(()), Ok(42), Done, Err(ForeignError(ProtocolFailure(NotPrepared))), Ok(()), Ok(99)), Closed), Closed)",
    );
}

#[test]
fn product_binding_refusals_precede_native_entry_and_keep_release() {
    for (body, fault) in [
        ("Sqlite.bind_int (statement, 0, 42)", "BadIndex"),
        ("Sqlite.bind_int (statement, 2147483648, 42)", "BadIndex"),
        (
            "Sqlite.bind_int (statement, 1, 9223372036854775807 + 1)",
            "BadInteger",
        ),
        (
            "Sqlite.bind_text (statement, 1, Sqlite.TextValue \"bad\\0text\")",
            "BadText",
        ),
    ] {
        let fixture = Fixture::new();
        let library = traced_product_library()
            .replace("\"sqlite3_prepare_v2\"", "\"probe_prepare\"")
            .replace("\"sqlite3_finalize\"", "\"probe_finalize\"")
            .replace("\"sqlite3_bind_int64\"", "\"probe_bind_int\"")
            .replace("\"sqlite3_bind_text\"", "\"probe_bind_text\"");
        fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
        fs::write(fixture.0.join("entry.ash"), format!("import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Unit>>> ! {{Sqlite.Initialize}}\nmain () = resource Sqlite.Connection<C> connection = Sqlite.InMemory {{\n    resource Sqlite.Statement<S, C> statement = (connection, \"SELECT ?1\") {{\n        {body}\n    }}\n}}\n")).unwrap();
        execute_product_fixture_with_trace(
            &fixture,
            &format!(
                "Completed(Completed(Err(ForeignError(InputFailure({fault}))), Closed), Closed)"
            ),
            Some((
                "initialize 0\nopen 0 1\nprepare 0 1\nfinalize 0\nclose 0\n",
                false,
            )),
        );
    }
}

#[test]
fn imported_product_sqlite_accepts_ascii_whitespace_tail() {
    product_probe(
        "Int",
        "42",
        "SELECT 42; \t\r\n",
        "Completed(Completed(42, Closed), Closed)",
    );
}

#[test]
fn imported_product_sqlite_copies_blob_empty_and_null_independently() {
    product_probe(
        "(Sqlite.Result<Sqlite.BytesOrNull>, Sqlite.Result<Sqlite.BytesOrNull>, Sqlite.Result<Sqlite.BytesOrNull>)",
        r#"match Sqlite.step statement {
            Sqlite.Row => (Sqlite.column_bytes (statement, 0), Sqlite.column_bytes (statement, 1), Sqlite.column_bytes (statement, 2))
            _ => (Sqlite.Err Sqlite.MissingRow, Sqlite.Err Sqlite.MissingRow, Sqlite.Err Sqlite.MissingRow)
        }"#,
        "SELECT X'010203', zeroblob(0), NULL",
        "Completed(Completed((Ok(BlobBytes([1, 2, 3])), Ok(BlobBytes([])), Ok(NullBytes)), Closed), Closed)",
    );
}

#[test]
fn imported_product_sqlite_copies_text_empty_null_and_embedded_nul_with_strict_utf8() {
    product_probe(
        "(Sqlite.Result<Sqlite.TextOrNull>, Sqlite.Result<Sqlite.TextOrNull>, Sqlite.Result<Sqlite.TextOrNull>, Sqlite.Result<Sqlite.TextOrNull>, Sqlite.Result<Sqlite.TextOrNull>)",
        r#"match Sqlite.step statement {
            Sqlite.Row => (Sqlite.column_text (statement, 0), Sqlite.column_text (statement, 1), Sqlite.column_text (statement, 2), Sqlite.column_text (statement, 3), Sqlite.column_text (statement, 4))
            _ => (Sqlite.Err Sqlite.MissingRow, Sqlite.Err Sqlite.MissingRow, Sqlite.Err Sqlite.MissingRow, Sqlite.Err Sqlite.MissingRow, Sqlite.Err Sqlite.MissingRow)
        }"#,
        "SELECT 'héllo', '', NULL, CAST(X'FF' AS TEXT), CAST(X'610062' AS TEXT)",
        "Completed(Completed((Ok(TextValue(\"héllo\")), Ok(TextValue(\"\")), Ok(NullText), Err(ForeignError(ConversionFailure)), Ok(TextValue(\"a\\0b\"))), Closed), Closed)",
    );
}

#[test]
fn imported_product_sqlite_binds_transient_bytes_text_and_null() {
    product_probe_with_imports(
        "import @builtin.string as T\n",
        "((Sqlite.Result<Unit>, Sqlite.Result<Unit>, Sqlite.Result<Unit>), (Sqlite.Result<Sqlite.BytesOrNull>, Sqlite.Result<Sqlite.TextOrNull>, Sqlite.Result<Sqlite.TextOrNull>))",
        r#"let bytes = T.to_utf8 "a\0b"
        let blob = Sqlite.bind_bytes (statement, 1, Sqlite.BlobBytes bytes)
        let text = Sqlite.bind_text (statement, 2, Sqlite.TextValue "héllo")
        let null = Sqlite.bind_text (statement, 3, Sqlite.NullText)
        let copied = match Sqlite.step statement {
            Sqlite.Row => (Sqlite.column_bytes (statement, 0), Sqlite.column_text (statement, 1), Sqlite.column_text (statement, 2))
            _ => (Sqlite.Err Sqlite.MissingRow, Sqlite.Err Sqlite.MissingRow, Sqlite.Err Sqlite.MissingRow)
        }
        ((blob, text, null), copied)"#,
        "SELECT ?1, ?2, ?3",
        "Completed(Completed(((Ok(()), Ok(()), Ok(())), (Ok(BlobBytes([97, 0, 98])), Ok(TextValue(\"héllo\")), Ok(NullText))), Closed), Closed)",
    );
}

#[test]
fn imported_product_sqlite_transient_inputs_survive_call_scratch() {
    product_probe_with_imports(
        "import @builtin.string as T\n",
        "((Sqlite.Result<Unit>, Sqlite.Result<Unit>, Sqlite.Result<Unit>), Sqlite.Result<Int>)",
        r#"let blob = Sqlite.bind_bytes (statement, 1, Sqlite.BlobBytes (T.to_utf8 "a\0b"))
        let text = Sqlite.bind_text (statement, 2, Sqlite.TextValue "héllo")
        let null = Sqlite.bind_bytes (statement, 3, Sqlite.NullBytes)
        let checked = match Sqlite.step statement {
            Sqlite.Row => Sqlite.column_int (statement, 0)
            _ => Sqlite.Err Sqlite.MissingRow
        }
        ((blob, text, null), checked)"#,
        "SELECT CASE WHEN typeof(?1) = 'blob' AND hex(?1) = '610062' AND typeof(?2) = 'text' AND ?2 = 'héllo' AND ?3 IS NULL THEN 42 ELSE 0 END",
        "Completed(Completed(((Ok(()), Ok(()), Ok(())), Ok(42)), Closed), Closed)",
    );
}

#[test]
fn imported_product_sqlite_copies_native_diagnostic_and_keeps_status() {
    for (bound, diagnostic) in [
        (327680, "Diagnostic(0, \"not an error\")"),
        (0, "DiagnosticUnavailable(0)"),
    ] {
        let fixture = Fixture::new();
        let library = traced_product_library();
        let probe = library.replace(
            "Foreign.copy_nul (view, 327680)",
            &format!("Foreign.copy_nul (view, {bound})"),
        );
        if bound == 0 {
            assert_ne!(library, probe);
        }
        fs::write(fixture.0.join("sqlite.ash"), probe).unwrap();
        fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Error> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = Sqlite.InMemory {\n    perform Sqlite.ConnectionOps<C>.diagnostic connection\n}\n").unwrap();
        println!("real product diagnostic bound {bound}");
        execute_product_fixture_with_trace(
            &fixture,
            &format!("Completed(ForeignError(NativeDiagnostic({diagnostic})), Closed)"),
            Some(("initialize 0\nopen 0 1\nclose 0\n", false)),
        );
    }
}

#[test]
fn product_native_diagnostic_after_prepare_failure_preserves_nonzero_status() {
    for bound in [327680, 0] {
        let fixture = Fixture::new();
        let library = traced_product_library()
            .replace("\"sqlite3_prepare_v2\"", "\"probe_prepare\"")
            .replace("\"sqlite3_finalize\"", "\"probe_finalize\"")
            .replace(
                "Foreign.copy_nul (view, 327680)",
                &format!("Foreign.copy_nul (view, {bound})"),
            );
        fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
        fs::write(fixture.0.join("entry.ash"), r#"import @ffi.sqlite as Sqlite
import @builtin.string as Text
main : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, (Int, Bool, Bool)> ! {Sqlite.Initialize}
main () = resource Sqlite.Connection<C> connection = Sqlite.InMemory {
    let _ = resource Sqlite.Statement<S, C> statement = (connection, "THIS IS NOT SQL") {
        true
    }
    let diagnostic = perform Sqlite.ConnectionOps<C>.diagnostic connection
    match diagnostic {
        Sqlite.ForeignError(Sqlite.NativeDiagnostic(Sqlite.Diagnostic(code, message))) => (code, false, Text.byte_length message == 0)
        Sqlite.ForeignError(Sqlite.NativeDiagnostic(Sqlite.DiagnosticUnavailable(code))) => (code, true, true)
        _ => (999, true, true)
    }
}
"#).unwrap();
        let expected = if bound == 0 {
            "Completed((1, true, true), Closed)"
        } else {
            "Completed((1, false, false), Closed)"
        };
        execute_product_fixture_with_trace(
            &fixture,
            expected,
            Some(("initialize 0\nopen 0 1\nprepare 1 0\nclose 0\n", false)),
        );
    }
}

#[test]
fn product_diagnostic_exact_associated_operation_context_checks_without_escape() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("sqlite.ash"),
        include_str!("../libraries/sqlite.ash"),
    )
    .unwrap();
    for (name, body) in [
        (
            "exact operation",
            "perform Sqlite.ConnectionOps<C>.diagnostic connection",
        ),
        (
            "annotated method",
            "let exact : Sqlite.Connection<C> -> Sqlite.Error ! {Sqlite.ConnectionOps<C>} = Sqlite.diagnostic\n    exact connection",
        ),
    ] {
        fs::write(fixture.0.join("entry.ash"), format!("import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Error> ! {{Sqlite.Initialize}}\nmain () = resource Sqlite.Connection<C> connection = Sqlite.InMemory {{\n    {body}\n}}\n")).unwrap();
        let result = compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
        });
        let compiled =
            result.unwrap_or_else(|failure| panic!("{name} diagnostic context: {failure:?}"));
        println!(
            "{name} diagnostic compilation: {:?}",
            compiled.compilation_work()
        );
    }
    for (name, body) in [
        (
            "State-return callable",
            "let exact : Sqlite.Connection<C> -> Sqlite.ConnectionState<C> ! {Sqlite.ConnectionOps<C>} = Sqlite.borrow\n    let ignored = exact connection\n    Sqlite.MissingRow",
        ),
        (
            "State-return closure",
            "let exact = fn(access) {\n        perform Sqlite.ConnectionOps<C>.borrow access\n    }\n    let ignored = exact connection\n    Sqlite.MissingRow",
        ),
        (
            "native wrapper",
            "let exact = fn(access) {\n        let state = perform Sqlite.ConnectionOps<C>.borrow access\n        perform Sqlite.ErrorCode<C>.call state\n    }\n    let ignored = exact connection\n    Sqlite.MissingRow",
        ),
    ] {
        fs::write(fixture.0.join("entry.ash"), format!("import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Error> ! {{Sqlite.Initialize}}\nmain () = resource Sqlite.Connection<C> connection = Sqlite.InMemory {{\n    {body}\n}}\n")).unwrap();
        let failure = compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
        })
        .expect_err(name);
        let expected = if name == "native wrapper" {
            "source owner operation requires its exact checked lifecycle phase"
        } else {
            "controlled native state is unavailable in ordinary callable types or captures"
        };
        assert!(
            format!("{failure:?}").contains(expected),
            "{name}: {failure:?}"
        );
    }
}

#[test]
fn imported_product_sqlite_opens_and_closes_one_connection() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("sqlite.ash"),
        include_str!("../libraries/sqlite.ash"),
    )
    .unwrap();
    fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Bool> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = (Sqlite.File \":memory:\") {\n    true\n}\n").unwrap();
    execute_product_fixture(&fixture, "Completed(true, Closed)");
}

#[test]
fn product_connection_counts_release_partial_cleanup_and_preopen_refusal() {
    for (path, expected, trace, initialize_failure) in [
        (
            ":memory:",
            "Completed(true, Closed)",
            "initialize 0\nopen 0 1\nclose 0\n",
            false,
        ),
        (
            "/dev/null/ash-sqlite-no-directory/database",
            "NotAcquired(NativeOpen(14))",
            "initialize 0\nopen 14 1\nclose 0\n",
            false,
        ),
        ("bad\0path", "NotAcquired(InvalidPath)", "", false),
        (
            ":memory:",
            "NotAcquired(InitializationFailed(77))",
            "initialize 77\n",
            true,
        ),
    ] {
        let fixture = Fixture::new();
        // Exact native names alone change in this observation fixture. The
        // wrapper forwards to real SQLite except the labelled init failure.
        let library = include_str!("../libraries/sqlite.ash")
            .replace("\"sqlite3_initialize\"", "\"probe_initialize\"")
            .replace("\"sqlite3_open_v2\"", "\"probe_open\"")
            .replace("\"sqlite3_close\"", "\"probe_close\"");
        fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
        fs::write(fixture.0.join("entry.ash"), format!("import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Bool> ! {{Sqlite.Initialize}}\nmain () = resource Sqlite.Connection<C> connection = (Sqlite.File {path:?}) {{\n    true\n}}\n")).unwrap();
        execute_product_fixture_with_trace(&fixture, expected, Some((trace, initialize_failure)));
    }
}

#[test]
fn retained_product_initializer_runs_once_before_one_native_acquisition() {
    let fixture = Fixture::new();
    fs::write(fixture.0.join("sqlite.ash"), traced_product_library()).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/initializer-once.ash"),
    )
    .unwrap();
    execute_product_fixture_with_trace(
        &fixture,
        "(Completed(42, Closed), 1)",
        Some(("initialize 0\nopen 0 1\nclose 0\n", false)),
    );
}

#[test]
fn retained_product_hidden_report_still_closes_the_native_connection() {
    let fixture = Fixture::new();
    fs::write(fixture.0.join("sqlite.ash"), traced_product_library()).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/hidden-report.ash"),
    )
    .unwrap();
    execute_product_fixture_with_trace(
        &fixture,
        "42",
        Some(("initialize 0\nopen 0 1\nclose 0\n", false)),
    );
}

#[test]
fn retained_product_repeated_workload_runs_through_generated_host() {
    let fixture = Fixture::new();
    let library = traced_product_library()
        .replace("\"sqlite3_prepare_v2\"", "\"probe_prepare\"")
        .replace("\"sqlite3_finalize\"", "\"probe_finalize\"");
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/repeated.ash"),
    )
    .unwrap();
    execute_product_fixture_with_trace(
        &fixture,
        "(Completed(Completed(Ok(42), Closed), Closed), Completed(Completed(Ok(42), Closed), Closed))",
        Some((
            "initialize 0\nopen 0 1\nprepare 0 1\nfinalize 0\nclose 0\ninitialize 0\nopen 0 1\nprepare 0 1\nfinalize 0\nclose 0\n",
            false,
        )),
    );
}

#[test]
fn retained_product_simultaneous_statements_run_through_generated_host() {
    let fixture = Fixture::new();
    let library = traced_product_library()
        .replace("\"sqlite3_prepare_v2\"", "\"probe_prepare\"")
        .replace("\"sqlite3_finalize\"", "\"probe_finalize\"");
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/simultaneous.ash"),
    )
    .unwrap();
    execute_product_fixture_with_trace(
        &fixture,
        "Completed(Completed(Ok(42), Closed), Closed)",
        Some((
            "initialize 0\nopen 0 1\nprepare 0 1\nprepare 0 1\nfinalize 0\nfinalize 0\nclose 0\n",
            false,
        )),
    );
}

#[test]
fn retained_product_copying_workload_runs_through_generated_host() {
    product_copying_workload(NativeLinkInput::SharedLibrary(PathBuf::from(
        "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0",
    )));
}

#[test]
fn retained_product_copying_workload_links_genuine_static_sqlite() {
    let archive = std::env::var_os("ASH_SQLITE_STATIC_ARCHIVE")
        .map(PathBuf::from)
        .expect("set ASH_SQLITE_STATIC_ARCHIVE to the genuine SQLite archive built by docs/tools/ash.md");
    assert!(
        archive.is_file(),
        "static SQLite input: {}",
        archive.display()
    );
    assert_sqlite_implementation_symbols(&archive);
    println!(
        "static SQLite implementation archive: bytes={} sha256={} path={}",
        fs::metadata(&archive).unwrap().len(),
        artifact_digest(&archive),
        archive.display()
    );
    product_copying_workload(NativeLinkInput::StaticArchive(archive));
}

fn product_copying_workload(native_input: NativeLinkInput) {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("sqlite.ash"),
        include_str!("../libraries/sqlite.ash"),
    )
    .unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/copying.ash"),
    )
    .unwrap();
    execute_product_fixture_with_native_input(
        &fixture,
        "CopySession(Completed(Completed(Ok(Copied(42, TextValue(\"héllo 世界\"), BlobBytes([0, 255]), TextValue(\"\"), BlobBytes([]), NullText, NullBytes, TextValue(\"世界\\0tail\"))), Closed), Closed))",
        None,
        native_input,
    );
}

#[test]
fn imported_product_sqlite_exposes_memory_and_file_acquisition_inputs() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("sqlite.ash"),
        include_str!("../libraries/sqlite.ash"),
    )
    .unwrap();
    for config in ["Sqlite.InMemory", "Sqlite.File \":memory:\""] {
        fs::write(fixture.0.join("entry.ash"), format!("import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Bool> ! {{Sqlite.Initialize}}\nmain () = resource Sqlite.Connection<C> connection = ({config}) {{\n    true\n}}\n")).unwrap();
        let compiled = compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
        })
        .unwrap_or_else(|failure| panic!("ordinary SQLite open configuration: {failure:?}"));
        println!(
            "open configuration source/Core: {:?}",
            compiled.compilation_work()
        );
    }
}

#[test]
fn retained_product_persistence_workload_runs_through_generated_host() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("sqlite.ash"),
        include_str!("../libraries/sqlite.ash"),
    )
    .unwrap();
    fs::write(
        fixture.0.join("rows.ash"),
        include_str!("fixtures/sqlite-product/rows.ash"),
    )
    .unwrap();
    let source = include_str!("fixtures/sqlite-product/session.ash").replace(
        "__SQLITE_FILE__",
        fixture.0.join("session.db").to_str().unwrap(),
    );
    fs::write(fixture.0.join("entry.ash"), source).unwrap();
    let unit = "Completed(Ok(()), Closed)";
    let rows = "Cons(Stored(1, TextValue(\"héllo 世界\"), BlobBytes([0, 255])), Cons(Stored(2, TextValue(\"héllo 世界\"), BlobBytes([0, 255])), Cons(Stored(3, TextValue(\"third\"), BlobBytes([])), Nil)))";
    let query = format!("Completed(Ok({rows}), Closed)");
    execute_product_fixture(
        &fixture,
        &format!(
            "SessionReports(Completed(({unit}, {unit}, {unit}, {unit}, {query}), Closed), Completed({query}, Closed))"
        ),
    );
}

#[test]
fn imported_product_sqlite_resumes_the_retained_copied_query() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("sqlite.ash"),
        include_str!("../libraries/sqlite.ash"),
    )
    .unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/control-resume.ash"),
    )
    .unwrap();
    execute_product_fixture(
        &fixture,
        "Completed(Completed(Ok(CopiedRow(TextValue(\"héllo 世界\"), BlobBytes([0, 255]))), Closed), Closed)",
    );
}

#[test]
fn retained_product_owned_discard_runs_cleanup_before_exact_native_release() {
    let fixture = Fixture::new();
    // These wrappers observe real calls; they neither inject outcomes nor
    // replace the passive declarations' ownership or conversion checks.
    let library = traced_product_library()
        .replace("\"sqlite3_prepare_v2\"", "\"probe_prepare\"")
        .replace("\"sqlite3_finalize\"", "\"probe_finalize\"")
        .replace("\"sqlite3_step\"", "\"probe_step\"")
        .replace("\"sqlite3_errcode\"", "\"probe_errcode\"")
        .replace("\"sqlite3_errmsg\"", "\"probe_errmsg\"");
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/control-discard.ash"),
    )
    .unwrap();
    execute_product_fixture_with_trace(
        &fixture,
        "42",
        Some((
            "initialize 0\nopen 0 1\nprepare 0 1\nerrcode 0\nerrmsg 0 1\nfinalize 0\nclose 0\n",
            false,
        )),
    );
}

#[test]
fn retained_product_protocol_refusals_precede_native_queries_and_mutations() {
    let fixture = Fixture::new();
    fs::write(fixture.0.join("sqlite.ash"), traced_statement_library()).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/protocol-refusals.ash"),
    )
    .unwrap();
    let not_prepared = "Err(ForeignError(ProtocolFailure(NotPrepared)))";
    execute_product_fixture_with_trace(
        &fixture,
        &format!(
            "Completed(Completed(Refusals(Err(ForeignError(ProtocolFailure(NotRow))), (Err(ForeignError(InputFailure(ColumnTypeMismatch))), Err(ForeignError(InputFailure(ColumnTypeMismatch))), Err(ForeignError(InputFailure(BadColumn))), Err(ForeignError(InputFailure(BadColumn)))), ({not_prepared}, {not_prepared}, {not_prepared}, {not_prepared}), (Row, Done, StepError(ForeignError(ProtocolFailure(AfterDone))))), Closed), Closed)"
        ),
        Some((
            "initialize 0\nopen 0 1\nprepare 0 1\nstep 100\ncolumn_count 3\ncolumn_type 3\ncolumn_count 3\ncolumn_type 2\ncolumn_count 3\nstep 101\nfinalize 0\nclose 0\n",
            false,
        )),
    );
}

#[test]
fn retained_product_prepare_refusals_preserve_partial_cleanup_and_diagnostic() {
    let fixture = Fixture::new();
    fs::write(fixture.0.join("sqlite.ash"), traced_statement_library()).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/prepare-refusals.ash"),
    )
    .unwrap();
    execute_product_fixture_with_trace(
        &fixture,
        r#"Completed(Refusals(NotAcquired(EmptySql), NotAcquired(InvalidTail), NotAcquired(InvalidSql), NotAcquired(PrepareFailed(1)), ForeignError(NativeDiagnostic(Diagnostic(1, "near \"SELEC\": syntax error")))), Closed)"#,
        Some((
            "initialize 0\nopen 0 1\nprepare 0 0\nprepare 0 1\nfinalize 0\nprepare 1 0\nerrcode 1\nerrmsg 0 1\nclose 0\n",
            false,
        )),
    );
}

#[test]
fn retained_product_constraint_failure_preserves_status_and_consumed_completion() {
    let fixture = Fixture::new();
    fs::write(fixture.0.join("sqlite.ash"), traced_statement_library()).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/constraint-failure.ash"),
    )
    .unwrap();
    let successful = "Completed(Ok(()), Closed)";
    execute_product_fixture_with_trace(
        &fixture,
        &format!(
            "Completed(({successful}, {successful}, Completed((Err(ForeignError(NativeStatus(19))), ForeignError(NativeDiagnostic(Diagnostic(19, \"UNIQUE constraint failed: t.id\")))), ConsumedError(NativeFinalize(19)))), Closed)"
        ),
        Some((
            "initialize 0\nopen 0 1\nprepare 0 1\nstep 101\nfinalize 0\nprepare 0 1\nstep 101\nfinalize 0\nprepare 0 1\nstep 19\nerrcode 19\nerrmsg 0 1\nfinalize 19\nclose 0\n",
            false,
        )),
    );
}

#[test]
fn retained_product_qualified_forwarding_chain_preserves_integer_and_completion() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("sqlite.ash"),
        include_str!("../libraries/sqlite.ash"),
    )
    .unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/forwarding-chain.ash"),
    )
    .unwrap();
    execute_product_fixture(&fixture, "Completed(Completed(Ok(42), Closed), Closed)");
}

#[test]
fn retained_product_reset_keeps_independent_copies_and_clear_restores_null() {
    let fixture = Fixture::new();
    let library = traced_product_library()
        .replace("\"sqlite3_prepare_v2\"", "\"probe_prepare\"")
        .replace("\"sqlite3_finalize\"", "\"probe_finalize\"")
        .replace("\"sqlite3_step\"", "\"probe_step\"")
        .replace("\"sqlite3_bind_text\"", "\"probe_bind_text\"")
        .replace("\"sqlite3_reset\"", "\"probe_reset\"")
        .replace("\"sqlite3_clear_bindings\"", "\"probe_clear_bindings\"");
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/reset-copies.ash"),
    )
    .unwrap();
    execute_product_fixture_with_trace(
        &fixture,
        "Completed(Completed(Ok(TextValue(\"héllo 世界\"), TextValue(\"héllo 世界\"), NullText), Closed), Closed)",
        Some((
            "initialize 0\nopen 0 1\nprepare 0 1\nbind_text 0\nstep 100\nreset 0\nstep 100\nreset 0\nclear_bindings 0\nstep 100\nstep 101\nfinalize 0\nclose 0\n",
            false,
        )),
    );
}

#[test]
fn retained_product_native_index_refusal_and_range_status_preserve_release() {
    let fixture = Fixture::new();
    fs::write(fixture.0.join("sqlite.ash"), traced_statement_library()).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        include_str!("fixtures/sqlite-product/native-indices.ash"),
    )
    .unwrap();
    execute_product_fixture_with_trace(
        &fixture,
        r#"Completed((Completed(Ok(-1), Closed), Completed(Err(ForeignError(InputFailure(BadIndex))), Closed), Completed((Err(ForeignError(NativeStatus(25))), ForeignError(NativeDiagnostic(Diagnostic(25, "column index out of range")))), Closed)), Closed)"#,
        Some((
            "initialize 0\nopen 0 1\nprepare 0 1\nstep 100\ncolumn_count 1\ncolumn_type 1\ncolumn_int 0\nfinalize 0\nprepare 0 1\nfinalize 0\nprepare 0 1\nbind_int 25\nerrcode 25\nerrmsg 0 1\nfinalize 0\nclose 0\n",
            false,
        )),
    );
}

#[test]
fn product_diagnostic_copy_is_ordinary_and_preserves_native_status() {
    let fixture = Fixture::new();
    let library = format!(
        "{}\n{}",
        include_str!("../libraries/sqlite.ash"),
        r#"
pub diagnostic_probe : Unit -> (Diagnostic, Diagnostic, Diagnostic)
diagnostic_probe () = {
    let refused = match Foreign.checked_nul "a\0b" {
        Foreign.Returned(_) => Foreign.Returned (Text.to_utf8 "unreachable")
        Foreign.ConversionFailed(error) => Foreign.ConversionFailed error
    }
    (diagnostic_copy (14, refused), diagnostic_copy (5, Foreign.Returned (Text.to_utf8 "")), diagnostic_copy (7, Foreign.Returned (Text.to_utf8 "message")))
}
"#
    );
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> (Sqlite.Diagnostic, Sqlite.Diagnostic, Sqlite.Diagnostic)\nmain () = Sqlite.diagnostic_probe ()\n").unwrap();
    let result = run_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap();
    assert_eq!(
        result.value_display(),
        "(DiagnosticUnavailable(14), Diagnostic(5, \"\"), Diagnostic(7, \"message\"))"
    );
}

#[test]
fn product_binding_input_policy_is_pure_before_native_entry() {
    let fixture = Fixture::new();
    let library = format!(
        "{}\n{}",
        include_str!("../libraries/sqlite.ash"),
        r#"
pub admission_probe : Unit -> (Result<Unit>, Result<Unit>, Result<Unit>, Result<Unit>, Result<Unit>, Result<Unit>, Result<Unit>, Result<Unit>, Result<Unit>)
admission_probe () = (
    binding_admission (0, 1),
    binding_admission (0, 0),
    binding_admission (0, NegativeOne),
    binding_admission (0, 2147483648),
    binding_admission (1, 0),
    text_binding_admission "",
    text_binding_admission "a\0b",
    binding_length_admission (2147483648, BadBytes),
    text_binding_admission "héllo"
)
"#
    );
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> (Sqlite.Result<Unit>, Sqlite.Result<Unit>, Sqlite.Result<Unit>, Sqlite.Result<Unit>, Sqlite.Result<Unit>, Sqlite.Result<Unit>, Sqlite.Result<Unit>, Sqlite.Result<Unit>, Sqlite.Result<Unit>)\nmain () = Sqlite.admission_probe ()\n").unwrap();
    // No native runtime or link input is installed. These are ordinary checks;
    // actual TRANSIENT calls remain a separate generated-host obligation.
    let observation = run_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("pure product input policy: {failure:?}"));
    assert_eq!(
        observation.value_display(),
        "(Ok(()), Err(ForeignError(InputFailure(BadIndex))), Err(ForeignError(InputFailure(BadIndex))), Err(ForeignError(InputFailure(BadIndex))), Err(ForeignError(ProtocolFailure(NotPrepared))), Ok(()), Err(ForeignError(InputFailure(BadText))), Err(ForeignError(InputFailure(BadBytes))), Ok(()))"
    );
}

#[test]
fn product_tail_whitespace_matches_the_retained_rust_policy() {
    let fixture = Fixture::new();
    let library = format!(
        "{}\n{}",
        include_str!("../libraries/sqlite.ash"),
        r#"
pub ascii_space_probe : Int -> Bool
ascii_space_probe byte = ascii_space byte
"#
    );
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    let bytes = [9_u8, 10, 11, 12, 13, 32, 0, 133];
    let calls = bytes
        .map(|byte| format!("Sqlite.ascii_space_probe {byte}"))
        .join(", ");
    fs::write(fixture.0.join("entry.ash"), format!("import @ffi.sqlite as Sqlite\nmain : Unit -> (Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool)\nmain () = ({calls})\n")).unwrap();
    // The retained Rust library uses this exact classifier for unused SQL.
    // This ordinary policy check has no native runtime or link input.
    let expected = format!(
        "({})",
        bytes
            .map(|byte| byte.is_ascii_whitespace().to_string())
            .join(", ")
    );
    let observation = run_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("pure SQL tail policy: {failure:?}"));
    assert_eq!(observation.value_display(), expected);
}

#[test]
fn product_tail_policy_checks_copied_byte_indices_without_native_authority() {
    let fixture = Fixture::new();
    let library = format!(
        "{}\n{}",
        include_str!("../libraries/sqlite.ash"),
        r#"
pub type TailByteProbe = TailByteResult(Bool)
    | InvalidTestByte
pub tail_byte_probe : (Int, Int) -> TailByteProbe
tail_byte_probe (byte, offset) = match B.append_byte (B.empty (), byte) {
    B.InvalidByte => InvalidTestByte
    B.BytesAppended(bytes) => TailByteResult (tail_whitespace (bytes, offset))
}
pub tail_string_probe : (String, Int) -> Bool
tail_string_probe value = valid_tail value
pub tail_negative_probe : Unit -> TailByteProbe
tail_negative_probe () = tail_byte_probe (32, NegativeOne)
"#
    );
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    let bytes = [
        (9, 0, true),
        (10, 0, true),
        (11, 0, false),
        (12, 0, true),
        (13, 0, true),
        (32, 0, true),
        (0, 0, false),
        (255, 0, false),
        (32, -1, false),
        (32, 1, true),
        (32, 2, false),
    ];
    let strings = [
        ("", 0, true),
        ("", 1, false),
        ("SELECT 42; \t\r\n", 10, true),
        ("SELECT 42; SELECT 43", 10, false),
        ("é ", 2, true),
        ("é ", 1, false),
        ("é ", 3, true),
        ("é ", 4, false),
        ("\0", 0, false),
    ];
    let mut calls = bytes
        .iter()
        .map(|(byte, offset, _)| {
            if *offset < 0 {
                "Sqlite.tail_negative_probe ()".to_owned()
            } else {
                format!("Sqlite.tail_byte_probe ({byte}, {offset})")
            }
        })
        .collect::<Vec<_>>();
    calls.extend(
        strings
            .iter()
            .map(|(sql, offset, _)| format!("Sqlite.tail_string_probe ({sql:?}, {offset})")),
    );
    let mut types = vec!["Sqlite.TailByteProbe"; bytes.len()];
    types.extend(vec!["Bool"; strings.len()]);
    fs::write(
        fixture.0.join("entry.ash"),
        format!(
            "import @ffi.sqlite as Sqlite\nmain : Unit -> ({})\nmain () = ({})\n",
            types.join(", "),
            calls.join(", ")
        ),
    )
    .unwrap();
    let mut expected = bytes
        .iter()
        .map(|(_, _, value)| format!("TailByteResult({value})"))
        .collect::<Vec<_>>();
    expected.extend(strings.iter().map(|(_, _, value)| value.to_string()));
    let observation = run_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("pure copied SQL-tail policy: {failure:?}"));
    assert_eq!(
        observation.value_display(),
        format!("({})", expected.join(", "))
    );
}

#[test]
fn product_prepare_native_status_precedes_absent_output_policy() {
    let fixture = Fixture::new();
    let library = format!(
        "{}\n{}",
        include_str!("../libraries/sqlite.ash"),
        r#"
pub prepare_status_probe : Unit -> (PrepareError, PrepareError, PrepareError, PrepareError, PrepareError, PrepareError)
prepare_status_probe () = (
    prepare_absent_output (0, EmptySql),
    prepare_absent_output (1, EmptySql),
    prepare_absent_output (NegativeOne, EmptySql),
    prepare_absent_output (0, InvalidTail),
    prepare_absent_output (1, InvalidTail),
    prepare_absent_output (NegativeOne, InvalidTail)
)
"#
    );
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> (Sqlite.PrepareError, Sqlite.PrepareError, Sqlite.PrepareError, Sqlite.PrepareError, Sqlite.PrepareError, Sqlite.PrepareError)\nmain () = Sqlite.prepare_status_probe ()\n").unwrap();
    // The status ordering is ordinary library policy. No native runtime is
    // installed; real SQLite failure/partial-owner cleanup is separate evidence.
    let observation = run_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("pure prepare status policy: {failure:?}"));
    assert_eq!(
        observation.value_display(),
        "(EmptySql, PrepareFailed(1), PrepareFailed(-1), InvalidTail, PrepareFailed(1), PrepareFailed(-1))"
    );
}

fn product_probe(body_type: &str, body: &str, sql: &str, expected: &str) {
    product_probe_with_imports("", body_type, body, sql, expected);
}

fn product_probe_with_imports(
    imports: &str,
    body_type: &str,
    body: &str,
    sql: &str,
    expected: &str,
) {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("sqlite.ash"),
        include_str!("../libraries/sqlite.ash"),
    )
    .unwrap();
    fs::write(fixture.0.join("entry.ash"), format!("import @ffi.sqlite as Sqlite\n{imports}main : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, {body_type}>> ! {{Sqlite.Initialize}}\nmain () = resource Sqlite.Connection<C> connection = (Sqlite.File \":memory:\") {{\n    resource Sqlite.Statement<S, C> statement = (connection, {sql:?}) {{\n        {body}\n    }}\n}}\n")).unwrap();
    execute_product_fixture(&fixture, expected);
}

fn execute_product_fixture(fixture: &Fixture, expected: &str) {
    execute_product_fixture_with_trace(fixture, expected, None);
}

fn traced_product_library() -> String {
    include_str!("../libraries/sqlite.ash")
        .replace("\"sqlite3_initialize\"", "\"probe_initialize\"")
        .replace("\"sqlite3_open_v2\"", "\"probe_open\"")
        .replace("\"sqlite3_close\"", "\"probe_close\"")
}

fn traced_statement_library() -> String {
    let mut library = traced_product_library();
    for (native, observed) in [
        ("sqlite3_prepare_v2", "probe_prepare"),
        ("sqlite3_finalize", "probe_finalize"),
        ("sqlite3_step", "probe_step"),
        ("sqlite3_errcode", "probe_errcode"),
        ("sqlite3_errmsg", "probe_errmsg"),
        ("sqlite3_column_count", "probe_column_count"),
        ("sqlite3_column_type", "probe_column_type"),
        ("sqlite3_column_int64", "probe_column_int"),
        ("sqlite3_bind_int64", "probe_bind_int"),
        ("sqlite3_bind_text", "probe_bind_text"),
        ("sqlite3_bind_blob", "probe_bind_blob"),
        ("sqlite3_clear_bindings", "probe_clear_bindings"),
    ] {
        library = library.replace(&format!("\"{native}\""), &format!("\"{observed}\""));
    }
    library
}

fn artifact_digest(path: &Path) -> String {
    let mut input = fs::File::open(path).unwrap();
    let mut hash = Sha256::new();
    let mut buffer = [0_u8; 16 * 1024];
    loop {
        let count = input.read(&mut buffer).unwrap();
        if count == 0 {
            break;
        }
        hash.update(&buffer[..count]);
    }
    format!("{:x}", hash.finalize())
}

fn assert_sqlite_implementation_symbols(path: &Path) {
    let output = Command::new("nm")
        .args(["-g", "--defined-only"])
        .arg(path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "SQLite implementation symbols: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let symbols = String::from_utf8(output.stdout).unwrap();
    for name in [
        "sqlite3_initialize",
        "sqlite3_open_v2",
        "sqlite3_prepare_v2",
        "sqlite3_step",
        "sqlite3_column_text",
        "sqlite3_column_blob",
        "sqlite3_finalize",
        "sqlite3_close",
    ] {
        let definitions = symbols
            .lines()
            .filter(|line| {
                let mut fields = line.split_whitespace();
                fields.next().is_some()
                    && fields.next() == Some("T")
                    && fields.next() == Some(name)
                    && fields.next().is_none()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            definitions.len(),
            1,
            "SQLite implementation {name}: {path:?}"
        );
        println!(
            "SQLite implementation {}: {}",
            path.display(),
            definitions[0]
        );
    }
}

fn execute_product_fixture_with_trace(
    fixture: &Fixture,
    expected: &str,
    counted: Option<(&str, bool)>,
) {
    execute_product_fixture_with_native_input(
        fixture,
        expected,
        counted,
        NativeLinkInput::SharedLibrary(PathBuf::from("/usr/lib/x86_64-linux-gnu/libsqlite3.so.0")),
    );
}

fn execute_product_fixture_with_native_input(
    fixture: &Fixture,
    expected: &str,
    counted: Option<(&str, bool)>,
    native_input: NativeLinkInput,
) {
    let static_sqlite = matches!(&native_input, NativeLinkInput::StaticArchive(_));
    assert!(!static_sqlite || counted.is_none());
    let compiled = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("product SQLite source/Core: {failure:?}"));
    println!(
        "product SQLite compilation: {:?}",
        compiled.compilation_work()
    );
    let executable = fixture.0.join("program");
    let mut configuration = BuildConfiguration::new(executable.clone());
    configuration.native_inputs = vec![native_input];
    if counted.is_some() {
        let source = fixture.0.join("trace.c");
        let object = fixture.0.join("trace.o");
        let archive = fixture.0.join("libtrace.a");
        fs::write(&source, include_str!("support/sqlite_connection_trace.c")).unwrap();
        let output = Command::new("cc")
            .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-c"])
            .arg(&source)
            .arg("-o")
            .arg(&object)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = Command::new("ar")
            .arg("crs")
            .arg(&archive)
            .arg(&object)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        for path in [&source, &object, &archive] {
            println!(
                "SQLite observation input {}: sha256={}",
                path.file_name().unwrap().to_str().unwrap(),
                artifact_digest(path)
            );
        }
        configuration
            .native_inputs
            .insert(0, NativeLinkInput::StaticArchive(archive));
    }
    configuration.cargo_target_directory =
        Some(PathBuf::from(std::env::var_os("CARGO_TARGET_DIR").unwrap()).join("ffi-native-hosts"));
    let prepared = prepare_program(&compiled, configuration)
        .unwrap_or_else(|failure| panic!("product SQLite native preparation: {failure:?}"));
    println!(
        "normal formula native preparation work: {}",
        prepared.preparation_work()
    );
    for source in fs::read_dir(&fixture.0).unwrap() {
        let source = source.unwrap().path();
        if source
            .extension()
            .is_some_and(|extension| extension == "ash")
        {
            fs::remove_file(source).unwrap();
        }
    }
    let built = build_prepared(prepared)
        .unwrap_or_else(|failure| panic!("product SQLite native build: {failure:?}"));
    if static_sqlite {
        assert_sqlite_implementation_symbols(&executable);
        let dynamic = Command::new("readelf")
            .arg("-d")
            .arg(&executable)
            .output()
            .unwrap();
        assert!(
            dynamic.status.success(),
            "static SQLite host dependency witness: {}",
            String::from_utf8_lossy(&dynamic.stderr)
        );
        let dynamic = String::from_utf8(dynamic.stdout).unwrap();
        for needed in dynamic.lines().filter(|line| line.contains("(NEEDED)")) {
            assert!(
                !needed.to_ascii_lowercase().contains("sqlite"),
                "static SQLite host retained a SQLite shared dependency: {needed}"
            );
            println!("static SQLite host dependency: {needed}");
        }
    }
    let generated = built.generated_source().parent().unwrap();
    let manifest = fs::read_to_string(generated.parent().unwrap().join("Cargo.toml")).unwrap();
    assert!(
        !manifest.contains("ash-foreign-adapter"),
        "product host must not depend on the experimental adapter"
    );
    let host_source = fs::read_to_string(built.generated_source()).unwrap();
    for legacy in ["sqlite_binding", "sqlite_manifest", "ash_sqlite_"] {
        assert!(
            !host_source.contains(legacy),
            "product host retained legacy SQLite path: {legacy}"
        );
    }
    for (role, path) in [
        ("executed_host", executable.clone()),
        ("generated_source", built.generated_source().to_path_buf()),
        ("private_image", generated.join("program-image.bin")),
        ("expected_facts", generated.join("expected-facts.bin")),
    ] {
        println!(
            "product SQLite artifact {role}: bytes={} sha256={}",
            fs::metadata(&path).unwrap().len(),
            artifact_digest(&path)
        );
    }
    if let Some(directory) = std::env::var_os("ASH_SQLITE_DIAGNOSTIC_DIR").map(PathBuf::from) {
        fs::create_dir_all(&directory).unwrap();
        for (input, name) in [
            (executable.as_path(), "program"),
            (built.generated_source(), "main.rs"),
            (
                generated.join("program-image.bin").as_path(),
                "program-image.bin",
            ),
            (
                generated.join("expected-facts.bin").as_path(),
                "expected-facts.bin",
            ),
        ] {
            fs::copy(input, directory.join(name)).unwrap();
        }
    }
    fs::remove_file(generated.join("program-image.bin")).unwrap();
    fs::remove_file(generated.join("expected-facts.bin")).unwrap();
    let mut command = Command::new(executable);
    command.env_remove("ASH_SQLITE_INITIALIZE_FAILURE");
    let trace = fixture.0.join("trace");
    if let Some((_, initialize_failure)) = counted {
        fs::write(&trace, "").unwrap();
        command.env("ASH_SQLITE_TRACE", &trace);
        if initialize_failure {
            command.env("ASH_SQLITE_INITIALIZE_FAILURE", "1");
        }
    }
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap().trim(), expected);
    if let Some((expected_trace, initialize_failure)) = counted {
        let trace = fs::read_to_string(trace).unwrap();
        println!(
            "product SQLite native trace (injected initialization failure={initialize_failure}):\n{trace}"
        );
        assert_eq!(trace, expected_trace);
    }
}
