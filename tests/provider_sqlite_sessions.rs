#[path = "support/sqlite_copying.rs"]
mod sqlite_copying_support;

use ash_foreign_adapter::Event;
use sqlite_copying_support::{
    Fixture, assert_closed_probe, assert_finish_dispatches, copied_sizes, in_row, probe,
    scope_failure,
};
use std::fs;

#[test]
fn statement_reuse_transactions_generic_rows_and_reopen_preserve_every_report() {
    let fixture = Fixture::new();
    let session = fixture.path("session-entry.ash");
    let database = fixture.path("session.sqlite3");
    let source = fs::read_to_string(&session).unwrap().replace(
        "\"__SQLITE_FILE__\"",
        &format!("{:?}", database.to_str().unwrap()),
    );
    fs::write(&session, source).unwrap();
    let (value, observations) = fixture.run("session-entry.ash");
    let unit = "Completed(Ok(()), Closed)";
    let rows = "Cons(Stored(1, TextValue(\"héllo 世界\"), BlobBytes([0, 255])), Cons(Stored(2, TextValue(\"héllo 世界\"), BlobBytes([0, 255])), Cons(Stored(3, TextValue(\"third\"), BlobBytes([])), Nil)))";
    let query = format!("Completed(Ok({rows}), Closed)");
    assert_eq!(
        value,
        format!(
            "SessionReports(Completed(({unit}, {unit}, {unit}, {unit}, {query}), Closed), Completed({query}, Closed))"
        )
    );
    for (operation, count) in [
        ("open", 2),
        ("close", 2),
        ("prepare", 6),
        ("finalize", 6),
        ("reset", 2),
        ("clear_bindings", 1),
        ("bind_int64", 3),
        ("bind_text_copy", 2),
        ("bind_blob_copy", 2),
        ("step", 14),
        ("column_int64", 6),
        ("column_text", 6),
        ("column_blob", 6),
    ] {
        assert_eq!(observations.calls(operation), count, "{operation}");
    }
    assert_eq!(
        copied_sizes(&observations),
        (
            vec![13, 2, 5, 0],
            vec![13, 2, 13, 2, 5, 0, 13, 2, 13, 2, 5, 0]
        )
    );
    assert_finish_dispatches(&observations, 6, 2);
    assert!(
        database.exists(),
        "SQLite must create the isolated database file"
    );
    let events = observations.events();
    let close_dispatches = events
        .iter()
        .enumerate()
        .filter_map(|(index, event)| {
            matches!(event, Event::FinishDispatched { operation: "close" }).then_some(index)
        })
        .collect::<Vec<_>>();
    let closes = events
        .iter()
        .enumerate()
        .filter_map(|(index, event)| {
            matches!(
                event,
                Event::Call {
                    operation: "close",
                    code: 0
                }
            )
            .then_some(index)
        })
        .collect::<Vec<_>>();
    let opens = events
        .iter()
        .enumerate()
        .filter_map(|(index, event)| {
            matches!(
                event,
                Event::Call {
                    operation: "open",
                    code: 0
                }
            )
            .then_some(index)
        })
        .collect::<Vec<_>>();
    assert!(
        closes[0] < opens[1],
        "persistence is read through a new connection"
    );
    assert_eq!(
        events[..close_dispatches[0]]
            .iter()
            .filter(|event| matches!(
                event,
                Event::Call {
                    operation: "finalize",
                    code: 0
                }
            ))
            .count(),
        5
    );
    assert_eq!(
        events[opens[1]..close_dispatches[1]]
            .iter()
            .filter(|event| matches!(
                event,
                Event::Call {
                    operation: "finalize",
                    code: 0
                }
            ))
            .count(),
        1
    );
}

#[test]
fn negative_parameter_index_from_an_independent_sqlite_integer_is_rejected() {
    let fixture = Fixture::new();
    let source = r#"import provider as Provider
import sqlite as Sqlite
type Probe = SourceFailure(Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Int>>)
| Target(Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Unit>>)
main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Probe>
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {
let negative = resource Sqlite.Statement<N> stmt = (db, Sqlite.SqlText "SELECT -1") {
match Sqlite.step stmt {
Sqlite.Row => Sqlite.column_int (stmt, 0)
Sqlite.Done => Sqlite.Err Sqlite.MissingRow
Sqlite.StepError(error) => Sqlite.Err error
}
}
match negative {
Provider.Completed(Sqlite.Ok(index), Provider.Closed) => Target (resource Sqlite.Statement<S> stmt = (db, Sqlite.SqlText "SELECT ?1") {
Sqlite.bind_int (stmt, index, 42)
})
unexpected => SourceFailure unexpected
}
}
"#;
    fs::write(fixture.path("negative-index.ash"), source).unwrap();
    let (value, observations) = fixture.run("negative-index.ash");
    assert_eq!(
        value,
        "Completed(Target(Completed(Err(ForeignError(InputFailure(BadIndex))), Closed)), Closed)"
    );
    for (operation, count) in [
        ("open", 1),
        ("prepare", 2),
        ("step", 1),
        ("column_int64", 1),
        ("bind_int64", 0),
        ("finalize", 2),
        ("close", 1),
    ] {
        assert_eq!(observations.calls(operation), count, "{operation}");
    }
}

#[test]
fn column_before_row_and_step_after_done_are_protocol_alternatives() {
    let fixture = Fixture::new();
    let (value, observations) = probe(
        &fixture,
        "SELECT 1",
        "discard_result (Sqlite.column_int (stmt, 0))",
    );
    assert_eq!(value, scope_failure("ProtocolFailure", "NotRow"));
    assert_closed_probe(&observations, 0);
    for operation in ["column_count", "column_type", "column_int64"] {
        assert_eq!(observations.calls(operation), 0, "{operation}");
    }
    let after_done = in_row(
        "match Sqlite.step stmt {\nSqlite.Done => step_result (Sqlite.step stmt)\nSqlite.Row => Sqlite.Err Sqlite.UnexpectedRow\nSqlite.StepError(error) => Sqlite.Err error\n}",
    );
    let (value, observations) = probe(&fixture, "SELECT 1", &after_done);
    assert_eq!(value, scope_failure("ProtocolFailure", "AfterDone"));
    assert_closed_probe(&observations, 2);
}

#[test]
fn binding_and_clear_after_a_row_reject_without_native_mutation() {
    let fixture = Fixture::new();
    for (body, operation) in [
        ("Sqlite.bind_int (stmt, 1, 42)", "bind_int64"),
        (
            "Sqlite.bind_text (stmt, 1, Sqlite.TextValue \"valid\")",
            "bind_text_copy",
        ),
        (
            "Sqlite.bind_bytes (stmt, 1, Sqlite.BlobBytes (B.empty ()))",
            "bind_blob_copy",
        ),
        ("Sqlite.clear_bindings stmt", "clear_bindings"),
    ] {
        let (value, observations) = probe(&fixture, "SELECT ?1", &in_row(body));
        assert_eq!(
            value,
            scope_failure("ProtocolFailure", "NotPrepared"),
            "{body}"
        );
        assert_closed_probe(&observations, 1);
        assert_eq!(observations.calls(operation), 0, "{operation}");
        assert_eq!(copied_sizes(&observations), (vec![], vec![]));
    }
}

#[test]
fn refused_empty_multiple_and_nul_sql_keep_acquisition_outcomes_and_guards() {
    let fixture = Fixture::new();
    for (sql, reason, prepares, finalizes) in [
        ("   ", "EmptySql", 1, 0),
        (
            "SELECT 1; SELECT 2",
            "PrepareFailure(InputFailure(MultipleStatements))",
            1,
            1,
        ),
        ("SELECT 1\0", "PrepareFailure(InputFailure(BadSql))", 0, 0),
    ] {
        let (value, observations) = probe(&fixture, sql, "Sqlite.Ok ()");
        assert_eq!(
            value,
            format!("Completed(NotAcquired({reason}), Closed)"),
            "{sql:?}"
        );
        for (operation, count) in [
            ("open", 1),
            ("prepare", prepares),
            ("step", 0),
            ("finalize", finalizes),
            ("close", 1),
        ] {
            assert_eq!(observations.calls(operation), count, "{sql:?}: {operation}");
        }
    }
    let source = r#"import provider as Provider
import sqlite as Sqlite
main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Unit>
main () = resource Sqlite.Connection<C> db = (Sqlite.File "bad\0path") {
()
}
"#;
    fs::write(fixture.path("bad-path.ash"), source).unwrap();
    let (value, observations) = fixture.run("bad-path.ash");
    assert_eq!(value, "NotAcquired(OpenFailure(InputFailure(BadPath)))");
    for operation in ["initialize", "open", "prepare", "close"] {
        assert_eq!(observations.calls(operation), 0, "{operation}");
    }
}

#[test]
fn malformed_sql_reports_the_real_native_code_and_copied_diagnostic() {
    let fixture = Fixture::new();
    let (value, observations) = probe(&fixture, "SELEC 1", "Sqlite.Ok ()");
    assert_eq!(
        value,
        "Completed(NotAcquired(PrepareFailure(NativeFailure(1, \"near \\\"SELEC\\\": syntax error\"))), Closed)"
    );
    for (operation, count) in [
        ("open", 1),
        ("prepare", 1),
        ("step", 0),
        ("finalize", 0),
        ("close", 1),
    ] {
        assert_eq!(observations.calls(operation), count, "{operation}");
    }
    assert!(observations.events().iter().any(|event| matches!(
        event,
        Event::Call {
            operation: "prepare",
            code: 1
        }
    )));
}

#[test]
fn genuine_constraint_failure_preserves_body_error_and_consumed_finalize_report() {
    let fixture = Fixture::new();
    let scope = "Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Unit>>";
    let source = format!(
        r#"import provider as Provider
import sqlite as Sqlite
main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, ({scope}, {scope}, {scope})>
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {{
let create = resource Sqlite.Statement<S> stmt = (db, Sqlite.SqlText "CREATE TABLE t(id INTEGER UNIQUE)") {{
step_result (Sqlite.step stmt)
}}
let first = resource Sqlite.Statement<S> stmt = (db, Sqlite.SqlText "INSERT INTO t VALUES (1)") {{
step_result (Sqlite.step stmt)
}}
let duplicate = resource Sqlite.Statement<S> stmt = (db, Sqlite.SqlText "INSERT INTO t VALUES (1)") {{
step_result (Sqlite.step stmt)
}}
(create, first, duplicate)
}}
step_result : Sqlite.StepResult -> Sqlite.Result<Unit>
step_result result = match result {{
Sqlite.Done => Sqlite.Ok ()
Sqlite.Row => Sqlite.Err Sqlite.UnexpectedRow
Sqlite.StepError(error) => Sqlite.Err error
}}
"#
    );
    fs::write(fixture.path("constraint-failure.ash"), source).unwrap();
    let (value, observations) = fixture.run("constraint-failure.ash");
    let successful = "Completed(Ok(()), Closed)";
    let native = "NativeFailure(19, \"UNIQUE constraint failed: t.id\")";
    assert_eq!(
        value,
        format!(
            "Completed(({successful}, {successful}, Completed(Err(ForeignError({native})), ConsumedError(FinalizeFailure({native})))), Closed)"
        )
    );
    for (operation, count) in [
        ("open", 1),
        ("prepare", 3),
        ("step", 3),
        ("finalize", 3),
        ("close", 1),
    ] {
        assert_eq!(observations.calls(operation), count, "{operation}");
    }
    let events = observations.events();
    for operation in ["step", "finalize"] {
        assert_eq!(events.iter().filter(|event| matches!(event, Event::Call { operation: found, code: 19 } if *found == operation)).count(), 1, "{operation}");
    }
    let failed_step = events
        .iter()
        .position(|event| {
            matches!(
                event,
                Event::Call {
                    operation: "step",
                    code: 19
                }
            )
        })
        .unwrap();
    let consumed_finalize = events
        .iter()
        .position(|event| {
            matches!(
                event,
                Event::Call {
                    operation: "finalize",
                    code: 19
                }
            )
        })
        .unwrap();
    let closed = events
        .iter()
        .position(|event| {
            matches!(
                event,
                Event::Call {
                    operation: "close",
                    code: 0
                }
            )
        })
        .unwrap();
    assert!(failed_step < consumed_finalize && consumed_finalize < closed);
}

#[test]
fn representable_parameter_outside_statement_preserves_sqlite_range_error() {
    let fixture = Fixture::new();
    let (value, observations) = probe(&fixture, "SELECT ?1", "Sqlite.bind_int (stmt, 2, 42)");
    assert!(
        value.starts_with("Completed(Completed(Err(ForeignError(NativeFailure(25, \""),
        "{value}"
    );
    assert!(value.ends_with("\"))), Closed), Closed)"), "{value}");
    assert_closed_probe(&observations, 0);
    assert_eq!(observations.calls("bind_int64"), 1);
    assert_eq!(observations.calls("errmsg"), 1);
    assert!(observations.events().contains(&Event::Call {
        operation: "bind_int64",
        code: 25,
    }));
    assert_eq!(copied_sizes(&observations), (vec![], vec![]));
}
