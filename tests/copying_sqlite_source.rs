//! The copying SQLite port starts at its real connection input/output contract.

use ash::{
    build::{BuildConfiguration, NativeLinkInput, build_prepared, prepare_program},
    driver::{RunConfiguration, compile_path},
    module::ModuleRoots,
};
use sha2::{Digest, Sha256};
use std::{
    fs,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

#[path = "support/sqlite_output_order.rs"]
mod sqlite_output_order;

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-copying-sqlite-source-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn imported_sqlite_connection_open_close_and_native_failure_use_the_source_contract() {
    for (path, expected) in [
        (":memory:", "Completed(42, Closed)"),
        (
            "/dev/null/ash-sqlite-no-directory/database",
            "NotAcquired(NativeOpen(14))",
        ),
        ("bad\0path", "NotAcquired(InvalidPath)"),
    ] {
        connection_probe(path, expected, None);
    }
}

#[test]
fn connection_counts_real_open_partial_cleanup_and_preopen_refusal() {
    for (path, expected, trace, initialize_failure) in [
        (
            ":memory:",
            "Completed(42, Closed)",
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
        connection_probe(path, expected, Some((trace, initialize_failure)));
    }
}

#[test]
fn sqlite_private_protocol_payload_changes_without_reacquiring_the_owner() {
    let library = CONNECTION
        .replace("data Unit", "data Int")
        .replace("Acquire<ConnectionState<C>, Unit, OpenError>", "Acquire<ConnectionState<C>, Int, OpenError>")
        .replace("Acquired(state, ())", "Acquired(state, 0)")
        .replace("is_open : Access -> Bool", "is_open : Access -> Int")
        .replace("is_open access => resume true", "is_open access => {\n            let before : Int = Foreign.data_of state\n            let _ = Foreign.replace_data (state, before + 1)\n            let after : Int = Foreign.data_of state\n            resume after\n        }");
    connection_program_probe(
        &library,
        "(Int, Int)",
        "(Sqlite.is_open db, Sqlite.is_open db)",
        ":memory:",
        "Completed((1, 2), Closed)",
        Some(("initialize 0\nopen 0 1\nclose 0\n", false)),
    );
}

#[test]
fn imported_sqlite_prepare_contract_retains_connection_and_extracts_input_tail() {
    for offset_first in [false, true] {
        statement_admission_probe(offset_first, None);
    }
}

#[test]
fn sqlite_prepare_output_orders_preserve_signature_and_contract_refusals() {
    for offset_first in [false, true] {
        for (before, after) in [
            (
                "output result as scalar",
                "output result as owner(StatementState<C, S>)",
            ),
            ("offset_into(1)", "offset_into(2)"),
            ("String, Int)", "Bytes, Int)"),
            (
                "readable result, readable 3, readable 4",
                "readable result, readable 3",
            ),
            ("out(pointer(InputAddress))", "out(pointer(Address))"),
            ("Foreign.Nullable<Int>", "Foreign.Nullable<Bool>"),
        ] {
            statement_admission_probe(offset_first, Some((before, after)));
        }
    }
}

fn statement_admission_probe(offset_first: bool, invalid: Option<(&str, &str)>) {
    let fixture = Fixture::new();
    let declarations = match invalid {
        Some((before, after)) => {
            assert!(STATEMENT_DECLARATIONS.contains(before));
            STATEMENT_DECLARATIONS.replacen(before, after, 1)
        }
        None => STATEMENT_DECLARATIONS.to_owned(),
    };
    let library = CONNECTION.replace(
        "    symbol Initialize",
        &format!("{declarations}    symbol Initialize"),
    );
    let library = if offset_first {
        sqlite_output_order::offset_first(&library)
    } else {
        library
    };
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        "import @ffi.sqlite as Sqlite\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    let result = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    });
    match invalid {
        None => {
            result.unwrap_or_else(|failure| panic!("checked SQLite statement/tail contract (offset first={offset_first}): {failure:?}"));
        }
        Some(case) => assert!(
            result.is_err(),
            "offset first={offset_first}, invalid={case:?}"
        ),
    }
}

#[test]
fn imported_access_family_has_an_original_constructor_free_nominal() {
    let fixture = Fixture::new();
    let access = r#"    access DiagnosticView<W, C> {
        window W
        owner ConnectionState<C>
        extent nul
        preserves ErrorCode
    }
    symbol ErrorCode<C> : ConnectionState<C> -> Foreign.Call<Int> {
        name "sqlite3_errcode"
        abi (pointer(Address)) -> CInt
        operand 0 from 0 current
        output result as scalar
        outcome otherwise { readable result }
    }
"#;
    fs::write(
        fixture.0.join("sqlite.ash"),
        CONNECTION.replace(
            "    symbol Initialize",
            &format!("{access}    symbol Initialize"),
        ),
    )
    .unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        "import @ffi.sqlite as Sqlite\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    let compiled = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("passive access-family nominal: {failure:?}"));
    println!(
        "passive access family compilation: {:?}",
        compiled.compilation_work()
    );
}

#[test]
fn declared_sqlite_column_view_and_extent_use_exact_source_contract() {
    let fixture = Fixture::new();
    let declarations = format!("{STATEMENT_DECLARATIONS}{COLUMN_VIEW_DECLARATIONS}");
    let library = CONNECTION.replace(
        "    symbol Initialize",
        &format!("{declarations}    symbol Initialize"),
    );
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        "import @ffi.sqlite as Sqlite\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("checked SQLite column view/extent: {failure:?}"));
}

const DIAGNOSTIC_VIEW_DECLARATIONS: &str = r#"    access DiagnosticView<W, C> {
        window W
        owner ConnectionState<C>
        extent nul
        preserves ErrorMessage
    }
    symbol ErrorMessage<W, C> : ConnectionState<C> -> Foreign.Call<Foreign.Output<Foreign.Nullable<DiagnosticView<W, C>>>> {
        name "sqlite3_errmsg"
        abi (pointer(Address)) -> pointer(InputAddress)
        operand 0 from 0 current
        output result as view(DiagnosticView<W, C>)
        outcome otherwise { readable result }
    }
"#;

#[test]
fn source_copy_window_introduces_only_a_fresh_lexical_view_context() {
    let fixture = Fixture::new();
    let declarations = DIAGNOSTIC_VIEW_DECLARATIONS;
    let library = CONNECTION
        .replace("    symbol Initialize", &format!("{declarations}    symbol Initialize"))
        .replace("is_open : Access -> Bool", "is_open : Access -> Int")
        .replace("is_open access => resume true", "is_open access => {\n            let copied = copy_window DiagnosticView<W, C> from state {\n                42\n            }\n            resume copied\n        }");
    fs::write(fixture.0.join("sqlite.ash"), &library).unwrap();
    fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Int> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = \":memory:\" {\n    Sqlite.is_open connection\n}\n").unwrap();
    let compiled = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("lexical copy window: {failure:?}"));
    println!(
        "lexical window compilation: {:?}",
        compiled.compilation_work()
    );
    let out_of_scope = library.replace(
        "resume copied",
        "let _ = perform ErrorMessage<W, C>.call state\n            resume copied",
    );
    fs::write(fixture.0.join("sqlite.ash"), out_of_scope).unwrap();
    let failure = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .expect_err("a retained declaration category must not bind W outside the lexical window");
    let failure = format!("{failure:?}");
    assert!(
        failure.contains("Resolution") && failure.contains("W"),
        "{failure}"
    );
}

#[test]
fn source_owner_scalar_borrow_refuses_blocked_finish_but_keeps_retained_access() {
    for (branch, original, succeeds) in [
        (
            "Foreign.Retained(code)",
            "Retained(state, NativeClose code)",
            true,
        ),
        (
            "Foreign.BlockedDependent",
            "Retained(state, BlockedByStatement)",
            false,
        ),
    ] {
        let fixture = Fixture::new();
        let library = include_str!("../libraries/sqlite.ash").replace(
            &format!("Foreign.Returned({branch}) => {original}"),
            &format!("Foreign.Returned({branch}) => {{\n            let _ = perform ErrorCode<C>.call state\n            {original}\n        }}"),
        );
        fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
        fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Bool> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> db = Sqlite.InMemory {\n    true\n}\n").unwrap();
        let result = compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
        });
        if succeeds {
            result.unwrap_or_else(|failure| {
                panic!("retained completion keeps exact scalar diagnostic access: {failure:?}")
            });
        } else {
            let failure =
                result.expect_err("blocked completion must not grant an ordinary native Borrow");
            assert!(
                format!("{failure:?}").contains("preserve the admitted owner flow"),
                "{failure:?}"
            );
        }
    }
}

#[test]
fn blocked_statement_keeps_a_live_enclosing_connection_diagnostic() {
    let fixture = Fixture::new();
    let library = include_str!("../libraries/sqlite.ash")
        .replace("finish (state, data) => match perform Finalize<C, S>.call state", "finish (state, (connection, phase)) => match perform Finalize<C, S>.call state")
        .replace("Foreign.Returned(Foreign.BlockedDependent) => Retained(state, InvalidFinalize)", "Foreign.Returned(Foreign.BlockedDependent) => {\n            let _ = perform ConnectionOps<C>.error_code connection\n            Retained(state, InvalidFinalize)\n        }");
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Bool> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> db = Sqlite.InMemory {\n    true\n}\n").unwrap();
    compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| {
        panic!("blocked child does not revoke its live enclosing connection: {failure:?}")
    });
}

#[test]
fn source_copy_window_refuses_a_blocked_owner_but_keeps_a_retained_owner() {
    for (branch, original, succeeds) in [
        (
            "Foreign.Retained(code)",
            "Retained(state, NativeClose code)",
            true,
        ),
        (
            "Foreign.BlockedDependent",
            "Retained(state, BlockedByStatement)",
            false,
        ),
    ] {
        let fixture = Fixture::new();
        let library = CONNECTION
            .replace("    symbol Initialize", &format!("{DIAGNOSTIC_VIEW_DECLARATIONS}    symbol Initialize"))
            .replace(&format!("Foreign.Returned({branch}) => {original}"),
                &format!("Foreign.Returned({branch}) => {{\n            let _ = copy_window DiagnosticView<W, C> from state {{\n                42\n            }}\n            {original}\n        }}"));
        fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
        fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Bool> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = \":memory:\" {\n    Sqlite.is_open connection\n}\n").unwrap();
        let result = compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
        });
        if succeeds {
            result.unwrap_or_else(|failure| {
                panic!("retained owner remains available for local cleanup: {failure:?}")
            });
        } else {
            let failure = result.expect_err("blocked close must not grant a new native window");
            assert!(
                format!("{failure:?}").contains("preserve the admitted owner flow"),
                "{failure:?}"
            );
        }
    }
}

#[test]
fn source_copy_window_authenticates_its_exact_original_view_query() {
    let fixture = Fixture::new();
    let declarations = DIAGNOSTIC_VIEW_DECLARATIONS;
    let library = CONNECTION
        .replace(
            "    symbol Initialize",
            &format!("{declarations}    symbol Initialize"),
        )
        .replace("is_open : Access -> Bool", "is_open : Access -> Int")
        .replace(
            "is_open access => resume true",
            r#"is_open access => {
            let copied = copy_window DiagnosticView<W, C> from state {
                match perform ErrorMessage<W, C>.call state {
                    Foreign.Returned(Foreign.Readable(Foreign.NonNull(view))) => 42
                    Foreign.Returned(_) => 41
                    Foreign.ConversionFailed(_) => 40
                }
            }
            resume copied
        }"#,
        );
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Int> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = \":memory:\" {\n    Sqlite.is_open connection\n}\n").unwrap();
    let compiled = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("original lexical view query: {failure:?}"));
    println!(
        "original view query compilation: {:?}",
        compiled.compilation_work()
    );
}

// Reuse the exact ordinary product policy, without importing unrelated port
// definitions into this bounded native diagnostic-window fixture.
fn diagnostic_policy() -> &'static str {
    let product = include_str!("../libraries/sqlite.ash");
    let start = product.find("pub type Diagnostic =").unwrap();
    let end = product.find("pub type NativeError =").unwrap();
    &product[start..end]
}

#[test]
fn sqlite_diagnostic_nul_copy_preserves_status_or_reports_unavailable() {
    for (bound, expected) in [
        (327_680, "Diagnostic(14, \"not an error\")"),
        (0, "DiagnosticUnavailable(14)"),
    ] {
        let body = format!(
            r#"is_open access => {{
            let copied = copy_window DiagnosticView<W, C> from state {{
                match perform ErrorMessage<W, C>.call state {{
                    Foreign.Returned(Foreign.Readable(Foreign.NonNull(view))) => Foreign.copy_nul (view, {bound})
                    Foreign.Returned(_) => Foreign.Returned (Text.to_utf8 "")
                    Foreign.ConversionFailed(error) => Foreign.ConversionFailed error
                }}
            }}
            resume diagnostic_copy (14, copied)
        }}"#
        );
        let library = CONNECTION
            .replace(
                "    symbol Initialize",
                &format!("{DIAGNOSTIC_VIEW_DECLARATIONS}    symbol Initialize"),
            )
            .replace("is_open : Access -> Bool", "is_open : Access -> Diagnostic")
            .replace("is_open access => resume true", &body);
        connection_program_probe(
            &format!(
                "import @builtin.string as Text\n{library}\n{}",
                diagnostic_policy()
            ),
            "Sqlite.Diagnostic",
            "Sqlite.is_open db",
            ":memory:",
            &format!("Completed({expected}, Closed)"),
            Some(("initialize 0\nopen 0 1\nclose 0\n", false)),
        );
    }
}

#[test]
fn sqlite_unavailable_diagnostic_keeps_native_open_status_and_disposes_partial_owner() {
    // Failure-only acquisition fixture: keep the native initialization/open
    // order, then exercise the unpublished guard without nested policy matches.
    // The ordinary product initialization/path policy has separate coverage.
    let start = CONNECTION.find("    acquire path => {").unwrap();
    let end = CONNECTION.find("    finish (state, data)").unwrap();
    let library = CONNECTION.replacen(&CONNECTION[start..end], r#"    acquire path => {
        let _ = perform Initialize.call ()
        match perform Open<C>.call path {
            Foreign.Returned((code, Foreign.Readable(Foreign.NonNull(state)))) => {
                let copied = copy_window DiagnosticView<W, C> from state {
                    match perform ErrorMessage<W, C>.call state {
                        Foreign.Returned(Foreign.Readable(Foreign.NonNull(view))) => Foreign.copy_nul (view, 0)
                        Foreign.Returned(_) => Foreign.Returned (Text.to_utf8 "")
                        Foreign.ConversionFailed(error) => Foreign.ConversionFailed error
                    }
                }
                Refused (NativeOpenDiagnostic (diagnostic_copy (code, copied)))
            }
            Foreign.Returned((code, _)) => Refused (NativeOpen code)
            Foreign.ConversionFailed(_) => Refused InvalidPath
        }
    }
"#, 1)
        .replace("    symbol Initialize", &format!("{DIAGNOSTIC_VIEW_DECLARATIONS}    symbol Initialize"))
        .replace("    | NativeOpen(Int)", "    | NativeOpen(Int)\n    | NativeOpenDiagnostic(Diagnostic)");
    connection_program_probe(
        &format!(
            "import @builtin.string as Text\n{library}\n{}",
            diagnostic_policy()
        ),
        "Int",
        "42",
        "/dev/null/ash-sqlite-no-directory/database",
        "NotAcquired(NativeOpenDiagnostic(DiagnosticUnavailable(14)))",
        Some(("initialize 0\nopen 14 1\nclose 0\n", false)),
    );
}

#[test]
fn source_copy_window_keeps_extent_query_on_the_exact_view_and_keys() {
    for (query_key, succeeds) in [("0", true), ("1", false)] {
        let fixture = Fixture::new();
        let library = CONNECTION.replace(
            "    symbol Initialize",
            &format!("{STATEMENT_DECLARATIONS}{COLUMN_VIEW_DECLARATIONS}    symbol Initialize"),
        );
        let start = STATEMENT_RESOURCE.find("select_value access => ").unwrap();
        let end = STATEMENT_RESOURCE[start..]
            .find("        prepared access")
            .unwrap()
            + start;
        let body = format!(
            r#"select_value access => {{
            let copied = copy_window ColumnView<W, C, S> from state {{
                match perform ColumnBlob<W, C, S>.call (state, 0) {{
                    Foreign.Returned(Foreign.Readable(Foreign.NonNull(view))) => {{
                        match perform ColumnBytes<W, C, S>.call (state, {query_key}, view) {{
                            Foreign.Returned(extent) => Foreign.extent_value extent
                            Foreign.ConversionFailed(_) => 40
                        }}
                    }}
                    Foreign.Returned(_) => 41
                    Foreign.ConversionFailed(_) => 40
                }}
            }}
            resume copied
        }}
"#
        );
        let resource = STATEMENT_RESOURCE.replacen(&STATEMENT_RESOURCE[start..end], &body, 1);
        // The enclosing connection's provider is the existing exact association,
        // used locally by Statement acquisition rather than stored as native D.
        let library = library
            .replace("ConnectionProvider<Access>", "ConnectionProvider<Access, State>")
            .replace("ConnectionOps<Access>", "ConnectionOps<Access, State>")
            .replace("    is_open : Access -> Bool", "    borrow : Access -> State ! {ConnectionOps<Access, State>}\n    is_open : Access -> Bool")
            .replace("    borrow : Access -> State ! {ConnectionOps<Access, State>}\n    is_open : Access -> Bool\n", "    borrow : Access -> State\n    is_open : Access -> Bool\n")
            .replace("provider ConnectionProvider<Connection<C>>", "provider ConnectionProvider<Connection<C>, ConnectionState<C>>")
            .replace("effect ConnectionOps<Connection<C>>", "effect ConnectionOps<Connection<C>, ConnectionState<C>>")
            .replace("        is_open access => resume true", "        borrow access => resume state\n        is_open access => resume true");
        fs::write(
            fixture.0.join("sqlite.ash"),
            format!("import @builtin.string as Text\n{library}\n{resource}"),
        )
        .unwrap();
        fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Int>> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = \":memory:\" {\n    resource Sqlite.Statement<C, S> statement = (connection, \"SELECT 42\") {\n        Sqlite.select_value statement\n    }\n}\n").unwrap();
        let result = compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
        });
        if succeeds {
            let compiled =
                result.unwrap_or_else(|failure| panic!("exact view/key extent: {failure:?}"));
            println!(
                "extent query compilation: {:?}",
                compiled.compilation_work()
            );
        } else {
            let failure =
                result.expect_err("literal mismatched column must reject before query execution");
            assert!(
                format!("{failure:?}").contains("preserve the admitted owner flow"),
                "{failure:?}"
            );
        }
    }
}

#[test]
fn source_copy_window_copies_real_sqlite_column_bytes() {
    real_column_copy_probe(false);
}

#[test]
fn sqlite_transient_blob_binding_copies_call_duration_input() {
    real_column_copy_probe(true);
}

#[test]
fn dynamic_extent_keys_refuse_before_the_native_length_query() {
    for key in [0, 1] {
        real_column_copy_probe_with_key(false, Some(key));
    }
}

#[test]
fn sqlite_input_extent_refusal_precedes_binding_and_preserves_owner_release() {
    let fixture = Fixture::new();
    let library = CONNECTION
        .replace("    symbol Initialize", &format!("{STATEMENT_DECLARATIONS}{TRANSIENT_BLOB_DECLARATIONS}    symbol Initialize"))
        .replace("ConnectionProvider<Access>", "ConnectionProvider<Access, State>")
        .replace("ConnectionOps<Access>", "ConnectionOps<Access, State>")
        .replace("    is_open : Access -> Bool ! {ConnectionOps<Access, State>}", "    borrow : Access -> State ! {ConnectionOps<Access, State>}\n    is_open : Access -> Bool ! {ConnectionOps<Access, State>}")
        .replace("    is_open : Access -> Bool\n", "    borrow : Access -> State\n    is_open : Access -> Bool\n")
        .replace("provider ConnectionProvider<Connection<C>>", "provider ConnectionProvider<Connection<C>, ConnectionState<C>>")
        .replace("effect ConnectionOps<Connection<C>>", "effect ConnectionOps<Connection<C>, ConnectionState<C>>")
        .replace("        is_open access => resume true", "        borrow access => resume state\n        is_open access => resume true")
        .replace("name \"sqlite3_initialize\"", "name \"probe_initialize\"")
        .replace("name \"sqlite3_open_v2\"", "name \"probe_open\"")
        .replace("name \"sqlite3_close\"", "name \"probe_close\"")
        .replace("name \"sqlite3_prepare_v2\"", "name \"probe_statement_prepare\"")
        .replace("name \"sqlite3_finalize\"", "name \"probe_statement_finalize\"")
        .replace("name \"sqlite3_bind_blob\"", "name \"probe_refused_bind_blob\"");
    let start = STATEMENT_RESOURCE.find("select_value access => ").unwrap();
    let end = start
        + STATEMENT_RESOURCE[start..]
            .find("        prepared access")
            .unwrap();
    let resource = STATEMENT_RESOURCE
        .replacen(
            &STATEMENT_RESOURCE[start..end],
            r#"select_value access => {
            let input = Text.to_utf8 "bound"
            match perform BindBlob<C, S>.call (state, 1, input, 6) {
                Foreign.ConversionFailed(_) => resume 777
                Foreign.Returned(_) => resume 999
            }
        }
"#,
            1,
        )
        .replace(
            "interpret Prepare<C, S>",
            "interpret BindBlob<C, S>, Prepare<C, S>",
        );
    fs::write(
        fixture.0.join("sqlite.ash"),
        format!("import @builtin.string as Text\n{library}\n{resource}"),
    )
    .unwrap();
    fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Int>> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = \":memory:\" {\n    resource Sqlite.Statement<C, S> statement = (connection, \"SELECT ?1\") {\n        Sqlite.select_value statement\n    }\n}\n").unwrap();
    // These observation wrappers retain the real SQLite acquisition/destruction
    // calls. Entering the selected bind callback aborts, making zero entry
    // independent of bytes under test or a release identity carried by them.
    let source = fixture.0.join("counted.c");
    fs::write(&source, format!("{COUNTED_CONNECTION}\n{COUNTED_STATEMENT}\nint probe_refused_bind_blob(void *statement, int index, const void *bytes, int length, void (*destroy)(void *)) {{ abort(); }}\n")).unwrap();
    let object = fixture.0.join("counted.o");
    assert!(
        Command::new("cc")
            .args(["-std=c11", "-c"])
            .arg(&source)
            .arg("-o")
            .arg(&object)
            .status()
            .unwrap()
            .success()
    );
    let archive = fixture.0.join("libcounted.a");
    assert!(
        Command::new("ar")
            .arg("crs")
            .arg(&archive)
            .arg(&object)
            .status()
            .unwrap()
            .success()
    );
    let compiled = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("input refusal source/Core: {failure:?}"));
    let executable = fixture.0.join("program");
    let mut configuration = BuildConfiguration::new(executable.clone());
    configuration.native_inputs = vec![
        NativeLinkInput::StaticArchive(archive),
        NativeLinkInput::SharedLibrary(PathBuf::from("/usr/lib/x86_64-linux-gnu/libsqlite3.so.0")),
    ];
    configuration.cargo_target_directory = Some(
        std::env::var_os("CARGO_TARGET_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
            .join("ffi-native-hosts"),
    );
    let prepared = prepare_program(&compiled, configuration).unwrap();
    for name in ["entry.ash", "sqlite.ash"] {
        fs::remove_file(fixture.0.join(name)).unwrap();
    }
    let built = build_prepared(prepared).unwrap();
    let generated = built.generated_source().parent().unwrap();
    for name in ["program-image.bin", "expected-facts.bin"] {
        fs::remove_file(generated.join(name)).unwrap();
    }
    let trace = fixture.0.join("trace");
    let output = Command::new(executable)
        .env("ASH_SQLITE_TRACE", &trace)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        "Completed(Completed(777, Closed), Closed)"
    );
    assert_eq!(
        fs::read_to_string(trace).unwrap(),
        "initialize 0\nopen 0 1\nprepare 0 1\nfinalize 0\nclose 0\n"
    );
}

fn real_column_copy_probe(bind_blob: bool) {
    real_column_copy_probe_with_key(bind_blob, None);
}

fn real_column_copy_probe_with_key(bind_blob: bool, dynamic_key: Option<i32>) {
    let fixture = Fixture::new();
    let mut library = CONNECTION
        .replace("    symbol Initialize", &format!("{STATEMENT_DECLARATIONS}{COLUMN_VIEW_DECLARATIONS}    symbol Initialize"))
        .replace("ConnectionProvider<Access>", "ConnectionProvider<Access, State>")
        .replace("ConnectionOps<Access>", "ConnectionOps<Access, State>")
        .replace("    is_open : Access -> Bool", "    borrow : Access -> State ! {ConnectionOps<Access, State>}\n    is_open : Access -> Bool")
        .replace("    borrow : Access -> State ! {ConnectionOps<Access, State>}\n    is_open : Access -> Bool\n", "    borrow : Access -> State\n    is_open : Access -> Bool\n")
        .replace("provider ConnectionProvider<Connection<C>>", "provider ConnectionProvider<Connection<C>, ConnectionState<C>>")
        .replace("effect ConnectionOps<Connection<C>>", "effect ConnectionOps<Connection<C>, ConnectionState<C>>")
        .replace("        is_open access => resume true", "        borrow access => resume state\n        is_open access => resume true");
    if bind_blob {
        library = library.replace(
            "    symbol Initialize",
            &format!("{TRANSIENT_BLOB_DECLARATIONS}    symbol Initialize"),
        );
    }
    let start = STATEMENT_RESOURCE.find("select_value access => ").unwrap();
    let end = STATEMENT_RESOURCE[start..]
        .find("        prepared access")
        .unwrap()
        + start;
    let body = r#"select_value access => match is_row (perform Step<C, S>.call state) {
            true => {
                let copied = copy_window ColumnView<W, C, S> from state {
                    match perform ColumnBlob<W, C, S>.call (state, 0) {
                        Foreign.Returned(Foreign.Readable(Foreign.NonNull(view))) => {
                            match perform ColumnBytes<W, C, S>.call (state, 0, view) {
                                Foreign.Returned(extent) => Foreign.copy_bytes (view, extent)
                                Foreign.ConversionFailed(error) => Foreign.ConversionFailed error
                            }
                        }
                        Foreign.Returned(_) => Foreign.Returned (Text.to_utf8 "null")
                        Foreign.ConversionFailed(error) => Foreign.ConversionFailed error
                    }
                }
                match copied {
                    Foreign.Returned(bytes) => resume bytes
                    Foreign.ConversionFailed(_) => resume (Text.to_utf8 "copy refused")
                }
            }
            false => resume (Text.to_utf8 "not row")
        }
"#;
    let body = if bind_blob {
        body.replace("select_value access => match", "select_value access => {\n            let input = Text.to_utf8 \"bound\"\n            let _ = perform BindBlob<C, S>.call (state, 1, input, 5)\n            match") + "        }\n"
    } else {
        body.to_string()
    };
    let body = if dynamic_key.is_some() {
        body.replace("select_value access =>", "select_value (access, index) =>")
            .replace(
                "ColumnBytes<W, C, S>.call (state, 0, view)",
                "ColumnBytes<W, C, S>.call (state, index, view)",
            )
    } else {
        body
    };
    let resource = STATEMENT_RESOURCE
        .replacen(&STATEMENT_RESOURCE[start..end], &body, 1)
        .replace(
            "select_value : Access -> Int",
            "select_value : Access -> Bytes",
        );
    let resource = if bind_blob {
        resource.replace(
            "interpret Prepare<C, S>",
            "interpret BindBlob<C, S>, Prepare<C, S>",
        )
    } else {
        resource
    };
    let resource = if dynamic_key.is_some() {
        resource.replace(
            "select_value : Access -> Bytes",
            "select_value : (Access, Int) -> Bytes",
        )
    } else {
        resource
    };
    if dynamic_key.is_some() {
        for (native, observed) in [
            ("sqlite3_initialize", "probe_initialize"),
            ("sqlite3_open_v2", "probe_open"),
            ("sqlite3_close", "probe_close"),
            ("sqlite3_prepare_v2", "probe_prepare"),
            ("sqlite3_finalize", "probe_finalize"),
            ("sqlite3_step", "probe_step"),
            ("sqlite3_column_blob", "probe_column_blob"),
            ("sqlite3_column_bytes", "probe_column_bytes"),
        ] {
            library = library.replace(&format!("\"{native}\""), &format!("\"{observed}\""));
        }
    }
    fs::write(
        fixture.0.join("sqlite.ash"),
        format!("import @builtin.string as Text\n{library}\n{resource}"),
    )
    .unwrap();
    fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Bytes>> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = \":memory:\" {\n    resource Sqlite.Statement<C, S> statement = (connection, \"SELECT X'010203'\") {\n        Sqlite.select_value statement\n    }\n}\n").unwrap();
    if bind_blob {
        let entry = fixture.0.join("entry.ash");
        fs::write(
            &entry,
            fs::read_to_string(&entry)
                .unwrap()
                .replace("SELECT X'010203'", "SELECT ?1"),
        )
        .unwrap();
    }
    if let Some(key) = dynamic_key {
        let entry = fixture.0.join("entry.ash");
        fs::write(
            &entry,
            fs::read_to_string(&entry).unwrap().replace(
                "Sqlite.select_value statement",
                &format!("Sqlite.select_value (statement, {key})"),
            ),
        )
        .unwrap();
    }
    let compiled = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("real SQLite copy source/Core: {failure:?}"));
    println!(
        "real column copy compilation: {:?}",
        compiled.compilation_work()
    );
    let executable = fixture.0.join("program");
    let mut configuration = BuildConfiguration::new(executable.clone());
    configuration.native_inputs = vec![NativeLinkInput::SharedLibrary(PathBuf::from(
        "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0",
    ))];
    if dynamic_key.is_some() {
        let source = fixture.0.join("trace.c");
        let object = fixture.0.join("trace.o");
        let archive = fixture.0.join("libtrace.a");
        fs::write(&source, COUNTED_CONNECTION).unwrap();
        for output in [
            Command::new("cc")
                .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-c"])
                .arg(&source)
                .arg("-o")
                .arg(&object)
                .output()
                .unwrap(),
            Command::new("ar")
                .arg("crs")
                .arg(&archive)
                .arg(&object)
                .output()
                .unwrap(),
        ] {
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        configuration
            .native_inputs
            .insert(0, NativeLinkInput::StaticArchive(archive));
    }
    configuration.cargo_target_directory = Some(
        std::env::var_os("CARGO_TARGET_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
            .join("ffi-native-hosts"),
    );
    // Optional local failure observation only. The fixture, budgets and
    // generated host are unchanged; retain exact inputs before normal disposal.
    let diagnostic = std::env::var_os("ASH_SQLITE_DIAGNOSTIC_DIR").map(PathBuf::from);
    if let Some(directory) = &diagnostic {
        fs::create_dir_all(directory).unwrap();
        for name in ["entry.ash", "sqlite.ash"] {
            fs::copy(fixture.0.join(name), directory.join(name)).unwrap();
        }
    }
    let prepared = prepare_program(&compiled, configuration)
        .unwrap_or_else(|failure| panic!("real SQLite copy native preparation: {failure:?}"));
    println!(
        "normal formula native preparation work: {}",
        prepared.preparation_work()
    );
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    fs::remove_file(fixture.0.join("sqlite.ash")).unwrap();
    let built = build_prepared(prepared)
        .unwrap_or_else(|failure| panic!("real SQLite copy generated build: {failure:?}"));
    let generated = built.generated_source().parent().unwrap();
    for (role, file) in [
        ("host", executable.clone()),
        ("runtime source", built.generated_source().to_path_buf()),
        ("image", generated.join("program-image.bin")),
        ("facts", generated.join("expected-facts.bin")),
    ] {
        let bytes = fs::read(file).unwrap();
        println!(
            "real column copy {role}: bytes={} sha256={:x}",
            bytes.len(),
            Sha256::digest(bytes)
        );
    }
    if let Some(directory) = &diagnostic {
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
        println!(
            "exact local SQLite startup observation: {}",
            directory.display()
        );
    }
    fs::remove_file(generated.join("program-image.bin")).unwrap();
    fs::remove_file(generated.join("expected-facts.bin")).unwrap();
    let trace = fixture.0.join("trace");
    let mut command = Command::new(executable);
    if dynamic_key.is_some() {
        command.env("ASH_SQLITE_TRACE", &trace);
        command.env_remove("ASH_SQLITE_INITIALIZE_FAILURE");
    }
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        if dynamic_key == Some(1) {
            "Completed(Completed([99, 111, 112, 121, 32, 114, 101, 102, 117, 115, 101, 100], Closed), Closed)"
        } else if bind_blob {
            "Completed(Completed([98, 111, 117, 110, 100], Closed), Closed)"
        } else {
            "Completed(Completed([1, 2, 3], Closed), Closed)"
        }
    );
    if let Some(key) = dynamic_key {
        let actual = fs::read_to_string(trace).unwrap();
        println!("dynamic extent key {key} actual native trace:\n{actual}");
        let query = if key == 0 { "column_bytes 0 3\n" } else { "" };
        assert_eq!(
            actual,
            format!(
                "initialize 0\nopen 0 1\nprepare 0 1\nstep 100\ncolumn_blob 0 1\n{query}finalize 0\nclose 0\n"
            )
        );
    }
}

#[test]
fn declared_sqlite_access_views_cannot_be_hidden_in_private_payloads() {
    use ash::{
        driver::{FileFailure, PipelineFailure},
        elaborate::TypeError,
    };
    for data in [
        "ColumnView<Unit, Unit, Unit>",
        "(ColumnView<Unit, Unit, Unit>, Int)",
        "HiddenView",
    ] {
        let fixture = Fixture::new();
        let declarations = format!("{STATEMENT_DECLARATIONS}{COLUMN_VIEW_DECLARATIONS}");
        let library = CONNECTION
            .replace(
                "    symbol Initialize",
                &format!("{declarations}    symbol Initialize"),
            )
            .replace("data Unit", &format!("data {data}"))
            .replace(
                "Acquire<ConnectionState<C>, Unit, OpenError>",
                &format!("Acquire<ConnectionState<C>, {data}, OpenError>"),
            );
        fs::write(
            fixture.0.join("sqlite.ash"),
            format!("{library}\npub type HiddenView = WrappedView(ColumnView<Unit, Unit, Unit>)\n"),
        )
        .unwrap();
        fs::write(
            fixture.0.join("entry.ash"),
            "import @ffi.sqlite as Sqlite\nmain : Unit -> Int\nmain () = 42\n",
        )
        .unwrap();
        let failure = compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
        })
        .expect_err("native views must be refused in D before checking lifecycle bodies");
        let FileFailure::Pipeline(context) = failure else {
            panic!("expected checked header refusal");
        };
        let PipelineFailure::Typing(TypeError::Source(diagnostic)) = context.failure() else {
            panic!(
                "expected source header refusal, got {:?}",
                context.failure()
            );
        };
        assert_eq!(
            diagnostic.primary.message(),
            "source resource header requires matching owned state, lifecycle symbols, and scope codecs",
            "{data}"
        );
    }
}

#[test]
fn generic_cell_n11_declared_views_cannot_be_payloads_or_hidden_in_wrappers() {
    use ash::{
        driver::{FileFailure, PipelineFailure},
        elaborate::TypeError,
    };
    let fixture = Fixture::new();
    let library = CONNECTION.replace(
        "    symbol Initialize",
        &format!("{STATEMENT_DECLARATIONS}{COLUMN_VIEW_DECLARATIONS}    symbol Initialize"),
    );
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    for (payload, initial) in [("Int", "41"), ("Wrapped<Int>", "Wrap(41)")] {
        fs::write(fixture.0.join("entry.ash"), format!("import @ffi.sqlite as Sqlite\nimport @builtin.generic_cell as Cell\ntype Wrapped<T> = Wrap(T)\nmain : Unit -> Int\nmain () = resource Cell.Cell<R,{payload}> c = ({initial}) {{\n42\n}}\n")).unwrap();
        let compiled = compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
        })
        .unwrap();
        assert_eq!(
            ash::driver::execute(&compiled).unwrap().value_display(),
            "42"
        );
    }
    for payload in [
        "Sqlite.ColumnView<Unit,Unit,Unit>",
        "(Int,Sqlite.ColumnView<Unit,Unit,Unit>)",
        "Wrapped<Sqlite.ColumnView<Unit,Unit,Unit>>",
    ] {
        fs::write(fixture.0.join("entry.ash"), format!("import @ffi.sqlite as Sqlite\nimport @builtin.generic_cell as Cell\ntype Wrapped<T> = Wrap(T)\nmain : Unit -> Int\nmain () = resource Cell.Cell<R,{payload}> c = 41 {{\n42\n}}\n")).unwrap();
        let failure = compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
        })
        .unwrap_err();
        assert_eq!(
            failure.reason_code(),
            "type.argument",
            "{payload}: {failure:?}"
        );
        let FileFailure::Pipeline(context) = failure else {
            panic!("checked public payload refusal")
        };
        let PipelineFailure::Typing(TypeError::Source(diagnostic)) = context.failure() else {
            panic!("source payload refusal: {:?}", context.failure())
        };
        assert_eq!(
            diagnostic.primary.message(),
            "controlled native state is unavailable in ordinary callable types or captures",
            "{payload}: {diagnostic:?}"
        );
    }
}

#[test]
fn pure_nul_preflight_has_an_explicit_ordinary_result() {
    for (input, expected) in [("", "true"), ("é/name", "true"), ("bad\0name", "false")] {
        let fixture = Fixture::new();
        fs::write(fixture.0.join("entry.ash"), format!("import @builtin.foreign as Foreign\nmain : Unit -> Bool\nmain () = match Foreign.checked_nul {input:?} {{\n    Foreign.Returned(_) => true\n    Foreign.ConversionFailed(_) => false\n}}\n")).unwrap();
        let compiled = compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .unwrap();
        assert_eq!(
            ash::driver::execute(&compiled).unwrap().value_display(),
            expected
        );
    }
}

#[test]
fn imported_connection_diagnostic_is_a_nonconsuming_guarded_native_call() {
    let fixture = Fixture::new();
    let declaration = "    symbol ErrorCode<C> : ConnectionState<C> -> Foreign.Call<Int> {\n        name \"sqlite3_errcode\"\n        abi (pointer(Address)) -> CInt\n        operand 0 from 0 current\n        output result as scalar\n        outcome otherwise { readable result }\n    }\n";
    let library = CONNECTION
        .replace("    symbol Initialize", &format!("{declaration}    symbol Initialize"))
        .replace("    is_open : Access -> Bool ! {ConnectionOps<Access>}", "    diagnostic_code : Access -> Int ! {ConnectionOps<Access>}\n    is_open : Access -> Bool ! {ConnectionOps<Access>}")
        .replace("    is_open : Access -> Bool\n", "    diagnostic_code : Access -> Int\n    is_open : Access -> Bool\n")
        .replace("interpret Open<C>, Close<C>", "interpret Open<C>, Close<C>, ErrorCode<C>")
        .replace("        is_open access => resume true", "        diagnostic_code access => match perform ErrorCode<C>.call state {\n            Foreign.Returned(code) => resume code\n            Foreign.ConversionFailed(_) => resume 999\n        }\n        is_open access => resume true");
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Int> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = \":memory:\" {\n    Sqlite.diagnostic_code connection\n}\n").unwrap();
    let compiled = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("guarded SQLite diagnostic: {failure:?}"));
    let executable = fixture.0.join("program");
    let mut configuration = BuildConfiguration::new(executable.clone());
    configuration.native_inputs = vec![NativeLinkInput::SharedLibrary(PathBuf::from(
        "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0",
    ))];
    configuration.cargo_target_directory = Some(
        std::env::var_os("CARGO_TARGET_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
            .join("ffi-native-hosts"),
    );
    let prepared = prepare_program(&compiled, configuration).unwrap();
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    fs::remove_file(fixture.0.join("sqlite.ash")).unwrap();
    let built = build_prepared(prepared).unwrap();
    let generated = built.generated_source().parent().unwrap();
    fs::remove_file(generated.join("program-image.bin")).unwrap();
    fs::remove_file(generated.join("expected-facts.bin")).unwrap();
    let output = Command::new(executable).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        "Completed(0, Closed)"
    );
}

#[test]
fn canonical_string_operations_restore_from_embedded_image_after_source_erasure() {
    let fixture = Fixture::new();
    let entry = fixture.0.join("entry.ash");
    fs::write(&entry, "import @builtin.string as Text\nmain : Unit -> (Int, Bool)\nmain () = match Text.from_utf8 (Text.to_utf8 \"é\") {\n    Text.Decoded(copied) => (Text.byte_length copied, Text.equal (copied, \"é\"))\n    Text.InvalidUtf8 => (999, false)\n}\n").unwrap();
    let compiled = compile_path(RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .unwrap();
    let executable = fixture.0.join("program");
    let mut configuration = BuildConfiguration::new(executable.clone());
    configuration.cargo_target_directory = Some(
        std::env::var_os("CARGO_TARGET_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
            .join("ffi-native-hosts"),
    );
    let prepared = prepare_program(&compiled, configuration).unwrap();
    fs::remove_file(entry).unwrap();
    let built = build_prepared(prepared).unwrap();
    let generated = built.generated_source().parent().unwrap();
    // Pure hosts embed IMAGE inline rather than producing external payloads.
    assert!(!generated.join("program-image.bin").exists());
    assert!(!generated.join("expected-facts.bin").exists());
    fs::remove_file(built.generated_source()).unwrap();
    let output = Command::new(executable).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        "(2, true)"
    );
}

#[test]
fn imported_nested_statement_prepares_and_finalizes_before_connection_close() {
    nested_statement_probe(false, false, false);
}

#[test]
fn offset_first_statement_preserves_native_reports_and_terminal_partial_owner_cleanup() {
    nested_statement_probe(false, false, true);
}

#[test]
fn statement_scalar_operand_refusal_does_not_enter_sqlite_or_consume_the_owner() {
    for offset_first in [false, true] {
        nested_statement_probe(true, false, offset_first);
    }
}

#[test]
fn statement_protocol_payload_update_preserves_the_parent_dependency() {
    for offset_first in [false, true] {
        nested_statement_probe(false, true, offset_first);
    }
}

#[test]
fn private_payload_capture_keeps_only_the_declared_outer_dependency() {
    let fixture = Fixture::new();
    let library = CONNECTION
        .replace("    symbol Initialize", &format!("{STATEMENT_DECLARATIONS}    symbol Initialize"))
        .replace("ConnectionProvider<Access>", "ConnectionProvider<Access, State>")
        .replace("ConnectionOps<Access>", "ConnectionOps<Access, State>")
        .replace("    is_open : Access -> Bool", "    borrow : Access -> State ! {ConnectionOps<Access, State>}\n    is_open : Access -> Bool")
        .replace("    borrow : Access -> State ! {ConnectionOps<Access, State>}\n    is_open : Access -> Bool\n", "    borrow : Access -> State\n    is_open : Access -> Bool\n")
        .replace("provider ConnectionProvider<Connection<C>>", "provider ConnectionProvider<Connection<C>, ConnectionState<C>>")
        .replace("effect ConnectionOps<Connection<C>>", "effect ConnectionOps<Connection<C>, ConnectionState<C>>")
        .replace("        is_open access => resume true", "        borrow access => resume state\n        is_open access => resume true");
    let resource = STATEMENT_RESOURCE
        .replace("StatementProvider<Access>", "StatementProvider<Access, C>")
        .replace("StatementOps<Access>", "StatementOps<Access, C>")
        .replace("StatementProvider<Statement<C, S>>", "StatementProvider<Statement<C, S>, C>")
        .replace("StatementOps<Statement<C, S>>", "StatementOps<Statement<C, S>, C>")
        .replace("    prepared : Access -> Bool", "    retained_parent : Access -> Connection<C> ! {StatementOps<Access, C>}\n    prepared : Access -> Bool")
        .replace("    retained_parent : Access -> Connection<C> ! {StatementOps<Access, C>}\n    prepared : Access -> Bool\n", "    retained_parent : Access -> Connection<C>\n    prepared : Access -> Bool\n")
        .replace("        prepared access => resume true", "        retained_parent access => match Foreign.data_of state {\n            (connection, _) => resume connection\n        }\n        prepared access => resume true");
    fs::write(
        fixture.0.join("sqlite.ash"),
        format!("import @builtin.string as Text\n{library}\n{resource}"),
    )
    .unwrap();
    fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Bool> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = \":memory:\" {\n    let report = resource Sqlite.Statement<C, S> statement = (connection, \"SELECT 42\") {\n        let parent : Sqlite.Connection<C> = Sqlite.retained_parent statement\n        parent\n    }\n    match report {\n        Sqlite.Completed(parent, Sqlite.Closed) => {\n            let _ : Sqlite.Connection<C> = parent\n            true\n        }\n        Sqlite.Completed(_, _) => false\n        Sqlite.NotAcquired(_) => false\n    }\n}\n").unwrap();
    compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| {
        panic!(
            "private D may return its declared live parent but never the closing child: {failure:?}"
        )
    });
}

fn nested_statement_probe(dynamic_index: bool, protocol: bool, offset_first: bool) {
    let fixture = Fixture::new();
    let start = STATEMENT_RESOURCE.find("select_value access => ").unwrap();
    let end = STATEMENT_RESOURCE[start..]
        .find("        prepared access")
        .unwrap()
        + start;
    let body = &STATEMENT_RESOURCE[start + "select_value access => ".len()..end];
    let body = body.replace("resume value", "resume (value + bias)");
    let resource = if protocol {
        let replacement = format!(
            "select_value access => {{\n            let before : (Connection<C>, Int) = Foreign.data_of state\n            let ready = match before {{\n                (connection, tail) => {{\n                    let _ = Foreign.replace_data (state, (connection, tail + 1))\n                    let after : (Connection<C>, Int) = Foreign.data_of state\n                    match after {{\n                        (_, updated) => updated == tail + 1\n                    }}\n                }}\n            }}\n            let bias = match ready {{\n                true => 0\n                false => 1000\n            }}\n            {body}\n        }}\n"
        );
        STATEMENT_RESOURCE.replacen(&STATEMENT_RESOURCE[start..end], &replacement, 1)
    } else if !dynamic_index {
        // Read the copied Int before the deep native-result branch. This keeps
        // the fixture within the unchanged parser structural-depth limit.
        let replacement = format!(
            "select_value access => {{\n            let before : (Connection<C>, Int) = Foreign.data_of state\n            let bias = match before {{\n                (_, tail) => match tail == 9 {{\n                    true => 0\n                    false => 1000\n                }}\n            }}\n            {body}\n        }}\n"
        );
        STATEMENT_RESOURCE.replacen(&STATEMENT_RESOURCE[start..end], &replacement, 1)
    } else {
        STATEMENT_RESOURCE.to_owned()
    };
    let library = CONNECTION
        .replace("    symbol Initialize", &format!("{STATEMENT_DECLARATIONS}    symbol Initialize"))
        .replace("ConnectionProvider<Access>", "ConnectionProvider<Access, State>")
        .replace("ConnectionOps<Access>", "ConnectionOps<Access, State>")
        .replace("    is_open : Access -> Bool", "    borrow : Access -> State ! {ConnectionOps<Access, State>}\n    is_open : Access -> Bool")
        .replace("    borrow : Access -> State ! {ConnectionOps<Access, State>}\n    is_open : Access -> Bool\n", "    borrow : Access -> State\n    is_open : Access -> Bool\n")
        .replace("provider ConnectionProvider<Connection<C>>", "provider ConnectionProvider<Connection<C>, ConnectionState<C>>")
        .replace("effect ConnectionOps<Connection<C>>", "effect ConnectionOps<Connection<C>, ConnectionState<C>>")
        .replace("        is_open access => resume true", "        borrow access => resume state\n        is_open access => resume true");
    let library = format!("import @builtin.string as Text\n{library}\n{resource}")
        .replace("\"sqlite3_initialize\"", "\"probe_initialize\"")
        .replace("\"sqlite3_open_v2\"", "\"probe_open\"")
        .replace("\"sqlite3_close\"", "\"probe_close\"")
        .replace("\"sqlite3_prepare_v2\"", "\"probe_statement_prepare\"")
        .replace("\"sqlite3_finalize\"", "\"probe_statement_finalize\"")
        .replace("\"sqlite3_step\"", "\"probe_statement_step\"")
        .replace("\"sqlite3_column_int64\"", "\"probe_column\"")
        // Retain the complete used two-owner probe, without the prototype's
        // unused Boolean provider operations.
        .replace(
            "    is_open : Access -> Bool ! {ConnectionOps<Access, State>}\n",
            "",
        )
        .replace("    is_open : Access -> Bool\n", "")
        .replace("        is_open access => resume true\n", "")
        .replace(
            "    prepared : Access -> Bool ! {StatementOps<Access>}\n",
            "",
        )
        .replace("    prepared : Access -> Bool\n", "")
        .replace("        prepared access => resume true\n", "");
    let library = if dynamic_index {
        library
            .replace("ColumnZero<C, S> : StatementState<C, S>", "Column<C, S> : (StatementState<C, S>, Int)")
            .replace("operand 1 from constant Ok", "operand 1 from 1 scalar")
            .replace("ColumnZero<C, S>", "Column<C, S>")
            .replace("perform Column<C, S>.call state", "perform Column<C, S>.call (state, 0)")
            .replace("Foreign.Returned(value) => resume value", "Foreign.Returned(value) => match perform Column<C, S>.call (state, 2147483648) {\n                    Foreign.ConversionFailed(_) => resume value\n                    Foreign.Returned(_) => resume 997\n                }")
    } else {
        library
    };
    let library = if offset_first {
        sqlite_output_order::offset_first(&library).replace(
            "\"probe_statement_prepare\"",
            "\"probe_statement_prepare_reversed\"",
        )
    } else {
        library
    };
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(fixture.0.join("entry.ash"), "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Int>> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = \":memory:\" {\n    resource Sqlite.Statement<C, S> statement = (connection, \"SELECT 42\") {\n        Sqlite.select_value statement\n    }\n}\n").unwrap();
    let compiled = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("nested SQLite statement: {failure:?}"));
    println!(
        "nested SQLite compilation: {:?}",
        compiled.compilation_work()
    );
    let executable = fixture.0.join("program");
    let mut configuration = BuildConfiguration::new(executable.clone());
    configuration.native_inputs = vec![NativeLinkInput::SharedLibrary(PathBuf::from(
        "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0",
    ))];
    let c_source = fixture.0.join("counted.c");
    let object = fixture.0.join("counted.o");
    let archive = fixture.0.join("libcounted.a");
    fs::write(
        &c_source,
        format!("{COUNTED_CONNECTION}\n{COUNTED_STATEMENT}"),
    )
    .unwrap();
    for output in [
        Command::new("cc")
            .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-c"])
            .arg(&c_source)
            .arg("-o")
            .arg(&object)
            .output()
            .unwrap(),
        Command::new("ar")
            .arg("crs")
            .arg(&archive)
            .arg(&object)
            .output()
            .unwrap(),
    ] {
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    configuration
        .native_inputs
        .insert(0, NativeLinkInput::StaticArchive(archive));
    configuration.cargo_target_directory = Some(
        std::env::var_os("CARGO_TARGET_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
            .join("ffi-native-hosts"),
    );
    let prepared = prepare_program(&compiled, configuration).unwrap();
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    fs::remove_file(fixture.0.join("sqlite.ash")).unwrap();
    let built = build_prepared(prepared).unwrap_or_else(|failure| {
        let log = failure
            .build_log()
            .and_then(|path| fs::read_to_string(path).ok())
            .unwrap_or_default();
        panic!("nested SQLite generated host: {failure:?}\n{log}")
    });
    let generated = built.generated_source().parent().unwrap();
    for (role, file) in [
        ("generated_source", built.generated_source().to_path_buf()),
        ("private_image", generated.join("program-image.bin")),
        ("expected_facts", generated.join("expected-facts.bin")),
        ("executed_host", executable.clone()),
        ("native_wrapper", c_source),
        ("native_archive", fixture.0.join("libcounted.a")),
    ] {
        let bytes = fs::read(&file).unwrap();
        println!(
            "SQLite statement artifact (offset first={offset_first}): {role}, bytes={}, sha256={:x}",
            bytes.len(),
            Sha256::digest(&bytes)
        );
    }
    fs::remove_file(generated.join("program-image.bin")).unwrap();
    fs::remove_file(generated.join("expected-facts.bin")).unwrap();
    for invalid_tail in [false, true] {
        let trace_path = fixture.0.join("trace");
        fs::write(&trace_path, "").unwrap();
        let mut command = Command::new(&executable);
        command
            .env("ASH_SQLITE_TRACE", &trace_path)
            .env_remove("ASH_SQLITE_INITIALIZE_FAILURE")
            .env_remove("ASH_SQLITE_INVALID_TAIL");
        if invalid_tail {
            command.env("ASH_SQLITE_INVALID_TAIL", "1");
        }
        let output = command.output().unwrap();
        let trace = fs::read_to_string(trace_path).unwrap();
        println!(
            "SQLite statement native trace (offset first={offset_first}, injected invalid tail={invalid_tail}):\n{trace}"
        );
        if invalid_tail {
            assert!(!output.status.success());
            assert!(
                output.stdout.is_empty(),
                "no ordinary report or source fallback"
            );
            assert_eq!(
                trace,
                "initialize 0\nopen 0 1\nprepare 0 1\nfinalize 0\nclose 0\n"
            );
        } else {
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(
                String::from_utf8(output.stdout).unwrap().trim(),
                "Completed(Completed(42, Closed), Closed)"
            );
            assert_eq!(
                trace,
                "initialize 0\nopen 0 1\nprepare 0 1\nstep 100\ncolumn 42\nfinalize 0\nclose 0\n"
            );
        }
    }
}

fn connection_probe(path: &str, expected: &str, counted: Option<(&str, bool)>) {
    connection_program_probe(CONNECTION, "Int", "42", path, expected, counted);
}

fn connection_program_probe(
    source: &str,
    body_type: &str,
    body: &str,
    path: &str,
    expected: &str,
    counted: Option<(&str, bool)>,
) {
    let fixture = Fixture::new();
    let library = if counted.is_some() {
        source
            .replace("\"sqlite3_initialize\"", "\"probe_initialize\"")
            .replace("\"sqlite3_open_v2\"", "\"probe_open\"")
            .replace("\"sqlite3_close\"", "\"probe_close\"")
    } else {
        source.to_owned()
    };
    fs::write(fixture.0.join("sqlite.ash"), library).unwrap();
    fs::write(
            fixture.0.join("entry.ash"),
            format!(
                "import @ffi.sqlite as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, {body_type}> ! {{Sqlite.Initialize}}\nmain () = resource Sqlite.Connection<C> db = {path:?} {{\n    {body}\n}}\n"
            ),
        )
        .unwrap();
    let compiled = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|failure| panic!("SQLite connection contract: {failure:?}"));
    println!("SQLite compilation: {:?}", compiled.compilation_work());
    let executable = fixture.0.join("program");
    let mut configuration = BuildConfiguration::new(executable.clone());
    configuration.native_inputs = vec![NativeLinkInput::SharedLibrary(PathBuf::from(
        "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0",
    ))];
    if counted.is_some() {
        let source = fixture.0.join("trace.c");
        let object = fixture.0.join("trace.o");
        let archive = fixture.0.join("libtrace.a");
        fs::write(&source, COUNTED_CONNECTION).unwrap();
        for result in [
            Command::new("cc")
                .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-c"])
                .arg(&source)
                .arg("-o")
                .arg(&object)
                .output()
                .unwrap(),
            Command::new("ar")
                .arg("crs")
                .arg(&archive)
                .arg(&object)
                .output()
                .unwrap(),
        ] {
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
        }
        configuration
            .native_inputs
            .insert(0, NativeLinkInput::StaticArchive(archive));
    }
    configuration.cargo_target_directory = Some(
        std::env::var_os("CARGO_TARGET_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
            .join("ffi-native-hosts"),
    );
    let prepared = prepare_program(&compiled, configuration).unwrap();
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    fs::remove_file(fixture.0.join("sqlite.ash")).unwrap();
    let built = build_prepared(prepared).unwrap_or_else(|failure| {
        let log = failure
            .build_log()
            .and_then(|path| fs::read_to_string(path).ok())
            .unwrap_or_default();
        panic!("SQLite generated host: {failure:?}\n{log}")
    });
    let generated = built.generated_source().parent().unwrap();
    for (role, file) in [
        ("generated_source", built.generated_source().to_path_buf()),
        ("private_image", generated.join("program-image.bin")),
        ("expected_facts", generated.join("expected-facts.bin")),
        ("executed_host", executable.clone()),
    ] {
        let bytes = fs::read(&file).unwrap();
        println!(
            "SQLite artifact {role}: bytes={} sha256={:x}",
            bytes.len(),
            Sha256::digest(&bytes)
        );
    }
    fs::remove_file(generated.join("program-image.bin")).unwrap();
    fs::remove_file(generated.join("expected-facts.bin")).unwrap();
    let trace_path = fixture.0.join("trace");
    let mut command = Command::new(executable);
    fs::write(&trace_path, "").unwrap();
    command.env("ASH_SQLITE_TRACE", &trace_path);
    command.env_remove("ASH_SQLITE_INITIALIZE_FAILURE");
    if counted.is_some_and(|(_, failure)| failure) {
        command.env("ASH_SQLITE_INITIALIZE_FAILURE", "1");
    }
    let output = command.output().unwrap();
    let trace = fs::read_to_string(&trace_path).unwrap();
    println!("SQLite actual native trace:\n{trace}");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap().trim(), expected);
    if let Some((expected_trace, _)) = counted {
        assert_eq!(trace, expected_trace);
    }
}

const CONNECTION: &str = include_str!("fixtures/sqlite-source-connection.ash");

const STATEMENT_DECLARATIONS: &str = r#"    repr I64 = signed(64)
    const Row : CInt = 100
    owner StatementState<C, S> {
        representation Address
        owned S
        retains C
        teardown Finalize
    }
    symbol Prepare<C, S> : (ConnectionState<C>, String, Int) -> Foreign.Call<(Int, Foreign.Output<Foreign.Nullable<StatementState<C, S>>>, Foreign.Output<Foreign.Nullable<Int>>)> {
        name "sqlite3_prepare_v2"
        abi (pointer(Address), pointer(InputAddress), CInt, out(pointer(Address)), out(pointer(InputAddress))) -> CInt
        operand 0 from 0 enclosing
        operand 1 from 1 nul call_borrow
        operand 2 from 2 scalar
        output result as scalar
        output 3 as owner(StatementState<C, S>)
        output 4 as offset_into(1)
        outcome result == Ok { readable result, readable 3, readable 4 }
        outcome otherwise { readable result, readable 3, unreadable 4 }
    }
    symbol Step<C, S> : StatementState<C, S> -> Foreign.Call<Int> {
        name "sqlite3_step"
        abi (pointer(Address)) -> CInt
        operand 0 from 0 current
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol ColumnZero<C, S> : StatementState<C, S> -> Foreign.Call<Int> {
        name "sqlite3_column_int64"
        abi (pointer(Address), CInt) -> I64
        operand 0 from 0 current
        operand 1 from constant Ok
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Finalize<C, S> : StatementState<C, S> -> Foreign.Call<Foreign.Disposition<Int>> {
        name "sqlite3_finalize"
        abi (pointer(Address)) -> CInt
        operand 0 from 0 current
        output result as scalar
        retained_dependents block
        outcome otherwise { readable result, consumed 0 }
    }
"#;

const TRANSIENT_BLOB_DECLARATIONS: &str = r#"    repr Destructor = function_address
    sentinel Transient : Destructor = all_bits_one
    symbol BindBlob<C, S> : (StatementState<C, S>, Int, Bytes, Int) -> Foreign.Call<Int> {
        name "sqlite3_bind_blob"
        abi (pointer(Address), CInt, pointer(InputAddress), CInt, Destructor) -> CInt
        operand 0 from 0 current
        operand 1 from 1 scalar
        operand 2 from 2 bytes(3) copy
        operand 3 from 3 scalar
        operand 4 from constant Transient
        output result as scalar
        outcome otherwise { readable result }
    }
"#;

const COLUMN_VIEW_DECLARATIONS: &str = r#"    access ColumnView<W, C, S> {
        window W
        owner StatementState<C, S>
        extent bytes
        preserves ColumnBlob, ColumnBytes
    }
    symbol ColumnBlob<W, C, S> : (StatementState<C, S>, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<ColumnView<W, C, S>>>> {
        name "sqlite3_column_blob"
        abi (pointer(Address), CInt) -> pointer(InputAddress)
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as view(ColumnView<W, C, S>, 1)
        outcome otherwise { readable result }
    }
    symbol ColumnBytes<W, C, S> : (StatementState<C, S>, Int, ColumnView<W, C, S>) -> Foreign.Call<Foreign.Extent<ColumnView<W, C, S>>> {
        name "sqlite3_column_bytes"
        abi (pointer(Address), CInt) -> CInt
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as extent_of(2, 1)
        outcome otherwise { readable result }
    }
"#;

const STATEMENT_RESOURCE: &str = r#"pub type PrepareError = InvalidSql
    | PrepareFailed(Int)
    | EmptySql
    | InvalidTail
pub type FinalizeError = NativeFinalize(Int)
    | InvalidFinalize
is_row : Foreign.Call<Int> -> Bool
is_row reply = match reply {
    Foreign.Returned(code) => code == Row
    Foreign.ConversionFailed(_) => false
}
pub interface StatementProvider<Access> {
    select_value : Access -> Int ! {StatementOps<Access>}
    prepared : Access -> Bool ! {StatementOps<Access>}
}
pub effect StatementOps<Access> {
    select_value : Access -> Int
    prepared : Access -> Bool
}
pub resource Statement<C, S> {
    owned S
    input (Connection<C>, String)
    state StatementState<C, S>
    data (Connection<C>, Int)
    acquisition Acquire<StatementState<C, S>, (Connection<C>, Int), PrepareError>
    completion Finish<StatementState<C, S>, FinalizeError>
    result Scope<PrepareError, FinalizeError, Answer> for <Answer>
    codec scope
    provider StatementProvider<Statement<C, S>>
    effect StatementOps<Statement<C, S>>
    interpret Prepare<C, S>, Finalize<C, S>, Step<C, S>, ColumnZero<C, S>
    acquire (connection, sql) => {
        let enclosing = perform ConnectionOps<Connection<C>, ConnectionState<C>>.borrow connection
        let length = Text.byte_length sql + 1
        match perform Prepare<C, S>.call (enclosing, sql, length) {
            Foreign.Returned((code, Foreign.Readable(Foreign.NonNull(state)), Foreign.Readable(Foreign.NonNull(tail)))) => match code == Ok {
                true => Acquired(state, (connection, tail))
                false => Refused (PrepareFailed code)
            }
            Foreign.Returned((code, Foreign.Readable(Foreign.Null), _)) => Refused EmptySql
            Foreign.Returned((code, _, Foreign.Readable(Foreign.Null))) => Refused InvalidTail
            Foreign.Returned((code, _, _)) => Refused (PrepareFailed code)
            Foreign.ConversionFailed(_) => Refused InvalidSql
        }
    }
    finish (state, data) => match perform Finalize<C, S>.call state {
        Foreign.Returned(Foreign.Consumed(code)) => match code == Ok {
            true => Consumed
            false => ConsumedFailure (NativeFinalize code)
        }
        Foreign.Returned(Foreign.Retained(code)) => Retained(state, NativeFinalize code)
        Foreign.Returned(Foreign.BlockedDependent) => Retained(state, InvalidFinalize)
        Foreign.ConversionFailed(_) => Retained(state, InvalidFinalize)
    }
    handlers (state, data) {
        select_value access => match is_row (perform Step<C, S>.call state) {
            true => match perform ColumnZero<C, S>.call state {
                Foreign.Returned(value) => resume value
                Foreign.ConversionFailed(_) => resume 999
            }
            false => resume 998
        }
        prepared access => resume true
    }
}
"#;

// Observation fixture only: generated Ash bridges still use exact authored
// signatures. The product library links SQLite directly, without this wrapper.
const COUNTED_CONNECTION: &str = include_str!("support/sqlite_connection_trace.c");

// The second execution deliberately violates only the tail-address contract
// AFTER a real successful SQLite prepare. This is extraction-failure injection,
// not a claim that SQLite itself returned an invalid address.
// Distinct wrapper names keep this oracle separate from the shared trace.
const COUNTED_STATEMENT: &str = r#"
#include <stdint.h>
#include <string.h>
extern int sqlite3_prepare_v2(void *, const char *, int, void **, const char **);
extern int sqlite3_finalize(void *);
extern int sqlite3_step(void *);
extern int64_t sqlite3_column_int64(void *, int);
int probe_statement_prepare(void *connection, const char *sql, int length, void **statement, const char **tail) {
    if (*statement || *tail || length != (int)strlen(sql) + 1) abort();
    int status = sqlite3_prepare_v2(connection, sql, length, statement, tail);
    trace("prepare", status, *statement != NULL);
    if (getenv("ASH_SQLITE_INVALID_TAIL")) *tail = (const char *)(uintptr_t)1;
    return status;
}
// This is a real reversed C signature. Forward to SQLite in its actual order.
int probe_statement_prepare_reversed(void *connection, const char *sql, int length, const char **tail, void **statement) {
    return probe_statement_prepare(connection, sql, length, statement, tail);
}
int probe_statement_finalize(void *statement) {
    int status = sqlite3_finalize(statement);
    trace("finalize", status, -1);
    return status;
}
int probe_statement_step(void *statement) {
    int status = sqlite3_step(statement);
    trace("step", status, -1);
    return status;
}
int64_t probe_column(void *statement, int column) {
    if (column) abort();
    int64_t value = sqlite3_column_int64(statement, column);
    trace("column", (int)value, -1);
    return value;
}
"#;
