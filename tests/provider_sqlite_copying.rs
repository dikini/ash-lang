#[path = "support/sqlite_copying.rs"]
mod sqlite_copying_support;

use ash_foreign_adapter::Event;
use sqlite_copying_support::{
    Fixture, assert_closed_probe, copied_sizes, in_row, probe, scope_failure,
};
use std::fs;

#[test]
fn copied_unicode_blobs_nulls_and_empty_values_survive_both_scopes() {
    let fixture = Fixture::new();
    let (value, observations) = fixture.run("copying-entry.ash");
    assert_eq!(
        value,
        "CopySession(Completed(Completed(Ok(Copied(42, TextValue(\"héllo 世界\"), BlobBytes([0, 255]), TextValue(\"\"), BlobBytes([]), NullText, NullBytes, TextValue(\"世界\\0tail\"))), Closed), Closed))"
    );
    for (operation, count) in [
        ("open", 1),
        ("prepare", 1),
        ("bind_int64", 1),
        ("bind_text_copy", 2),
        ("bind_blob_copy", 2),
        ("bind_null", 2),
        ("step", 2),
        ("column_int64", 1),
        ("column_text", 3),
        ("column_blob", 2),
        ("finalize", 1),
        ("close", 1),
    ] {
        assert_eq!(observations.calls(operation), count, "{operation}");
    }
    assert_eq!(
        copied_sizes(&observations),
        (vec![13, 2, 0, 0], vec![13, 2, 0, 0, 11])
    );
    assert_closed_probe(&observations, 2);
    let events = observations.events();
    let index = |name| {
        events
            .iter()
            .position(
                |event| matches!(event, Event::Call { operation, code: 0 } if *operation == name),
            )
            .unwrap()
    };
    assert!(index("finalize") < index("close"));
}

#[test]
fn imported_unicode_text_binding_returns_an_independent_copy_after_completion() {
    let fixture = Fixture::new();
    let (value, observations) = fixture.run("text-entry.ash");
    assert_eq!(
        value,
        "Completed(Completed(Ok(TextValue(\"héllo 世界\")), Closed), Closed)"
    );
    assert_closed_probe(&observations, 1);
    assert_eq!(observations.calls("bind_text_copy"), 1);
    assert_eq!(observations.calls("column_text"), 1);
    assert_eq!(copied_sizes(&observations), (vec![13], vec![13]));
}

#[test]
fn bound_text_nul_is_an_ordinary_failure_with_both_completion_reports() {
    let fixture = Fixture::new();
    let entry = fixture.path("copying-entry.ash");
    let source = fs::read_to_string(&entry).unwrap().replace(
        "Sqlite.TextValue \"héllo 世界\"",
        "Sqlite.TextValue \"nul\\0text\"",
    );
    fs::write(entry, source).unwrap();
    let (value, observations) = fixture.run("copying-entry.ash");
    assert_eq!(
        value,
        "CopySession(Completed(Completed(Err(ForeignError(InputFailure(BadText))), Closed), Closed))"
    );
    for (operation, count) in [
        ("open", 1),
        ("prepare", 1),
        ("bind_int64", 1),
        ("bind_text_copy", 0),
        ("step", 0),
        ("finalize", 1),
        ("close", 1),
    ] {
        assert_eq!(observations.calls(operation), count, "{operation}");
    }
    assert_eq!(copied_sizes(&observations), (vec![], vec![]));
    assert_closed_probe(&observations, 0);
}

#[test]
fn integer_width_and_nonnegative_parameter_index_fail_before_native_binding() {
    let fixture = Fixture::new();
    let huge = "999999999999999999999999999999999999999999999999999999";
    for (operand, reason) in [
        (format!("(stmt, 1, {huge})"), "BadInteger"),
        ("(stmt, 0, 1)".into(), "BadIndex"),
        (format!("(stmt, {huge}, 1)"), "BadIndex"),
    ] {
        let (value, observations) =
            probe(&fixture, "SELECT ?1", &format!("Sqlite.bind_int {operand}"));
        assert_eq!(value, scope_failure("InputFailure", reason), "{operand}");
        assert_closed_probe(&observations, 0);
        assert_eq!(observations.calls("bind_int64"), 0);
    }
}

#[test]
fn wrong_storage_kind_and_bad_column_are_distinct_from_protocol_errors() {
    let fixture = Fixture::new();
    for sql in ["SELECT 'text'", "SELECT CAST(x'ff' AS TEXT)"] {
        let (value, observations) = probe(
            &fixture,
            sql,
            &in_row("discard_result (Sqlite.column_int (stmt, 0))"),
        );
        assert_eq!(
            value,
            scope_failure("InputFailure", "ColumnTypeMismatch"),
            "{sql}"
        );
        assert_closed_probe(&observations, 1);
        assert_eq!(observations.calls("column_type"), 1);
        assert_eq!(observations.calls("column_int64"), 0);
        assert_eq!(observations.calls("column_text"), 0);
        assert_eq!(copied_sizes(&observations), (vec![], vec![]));
    }
    for (index, count_queries) in [("1", 1), ("999999999999999999999999999999", 0)] {
        let (value, observations) = probe(
            &fixture,
            "SELECT 1",
            &in_row(&format!(
                "discard_result (Sqlite.column_int (stmt, {index}))"
            )),
        );
        assert_eq!(value, scope_failure("InputFailure", "BadColumn"), "{index}");
        assert_closed_probe(&observations, 1);
        assert_eq!(observations.calls("column_count"), count_queries);
        assert_eq!(observations.calls("column_type"), 0);
        assert_eq!(observations.calls("column_int64"), 0);
    }
}

#[test]
fn malformed_native_text_and_float_columns_preserve_copy_and_type_failures() {
    let fixture = Fixture::new();
    let (value, observations) = probe(
        &fixture,
        "SELECT CAST(x'ff' AS TEXT)",
        &in_row("discard_result (Sqlite.column_text (stmt, 0))"),
    );
    assert_eq!(
        value,
        "Completed(Completed(Err(ForeignError(ConversionFailure)), Closed), Closed)"
    );
    assert_closed_probe(&observations, 1);
    assert_eq!(observations.calls("column_text"), 1);
    assert_eq!(observations.calls("column_bytes"), 1);
    assert_eq!(copied_sizes(&observations), (vec![], vec![1]));

    let (value, observations) = probe(
        &fixture,
        "SELECT 1.5",
        &in_row("discard_result (Sqlite.column_int (stmt, 0))"),
    );
    assert_eq!(value, scope_failure("InputFailure", "ColumnTypeMismatch"));
    assert_closed_probe(&observations, 1);
    assert_eq!(observations.calls("column_type"), 1);
    assert_eq!(observations.calls("column_int64"), 0);
    assert_eq!(copied_sizes(&observations), (vec![], vec![]));
}

#[test]
fn reset_preserves_bound_text_and_clear_restores_null_after_copied_results() {
    let fixture = Fixture::new();
    let source = r#"import provider as Provider
import sqlite as Sqlite
main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<(Sqlite.TextOrNull, Sqlite.TextOrNull, Sqlite.TextOrNull)>>>
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {
resource Sqlite.Statement<S> stmt = (db, Sqlite.SqlText "SELECT ?1") {
match Sqlite.bind_text (stmt, 1, Sqlite.TextValue "héllo 世界") {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(()) => match read_text stmt {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(first) => after_first (stmt, first)
}
}
}
}
read_text<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Sqlite.TextOrNull> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
read_text stmt = match Sqlite.step stmt {
Sqlite.Row => Sqlite.column_text (stmt, 0)
Sqlite.Done => Sqlite.Err Sqlite.MissingRow
Sqlite.StepError(error) => Sqlite.Err error
}
after_first<S, C> : (Sqlite.Statement<S, C>, Sqlite.TextOrNull) -> Sqlite.Result<(Sqlite.TextOrNull, Sqlite.TextOrNull, Sqlite.TextOrNull)> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
after_first (stmt, first) = match Sqlite.reset stmt {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(()) => match read_text stmt {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(second) => after_second (stmt, first, second)
}
}
after_second<S, C> : (Sqlite.Statement<S, C>, Sqlite.TextOrNull, Sqlite.TextOrNull) -> Sqlite.Result<(Sqlite.TextOrNull, Sqlite.TextOrNull, Sqlite.TextOrNull)> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
after_second (stmt, first, second) = match Sqlite.reset stmt {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(()) => match Sqlite.clear_bindings stmt {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(()) => read_cleared (stmt, first, second)
}
}
read_cleared<S, C> : (Sqlite.Statement<S, C>, Sqlite.TextOrNull, Sqlite.TextOrNull) -> Sqlite.Result<(Sqlite.TextOrNull, Sqlite.TextOrNull, Sqlite.TextOrNull)> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
read_cleared (stmt, first, second) = match read_text stmt {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(cleared) => match Sqlite.step stmt {
Sqlite.Done => Sqlite.Ok (first, second, cleared)
Sqlite.Row => Sqlite.Err Sqlite.UnexpectedRow
Sqlite.StepError(error) => Sqlite.Err error
}
}
"#;
    fs::write(fixture.path("reset-copying.ash"), source).unwrap();
    let (value, observations) = fixture.run("reset-copying.ash");
    assert_eq!(
        value,
        "Completed(Completed(Ok(TextValue(\"héllo 世界\"), TextValue(\"héllo 世界\"), NullText), Closed), Closed)"
    );
    assert_closed_probe(&observations, 4);
    for (operation, count) in [
        ("bind_text_copy", 1),
        ("reset", 2),
        ("clear_bindings", 1),
        ("column_text", 2),
    ] {
        assert_eq!(observations.calls(operation), count, "{operation}");
    }
    assert_eq!(copied_sizes(&observations), (vec![13], vec![13, 13]));
}

#[test]
fn qualified_forwarding_chain_preserves_integer_and_source_completion() {
    let fixture = Fixture::new();
    for (name, source) in [
        (
            "forwarding-chain.ash",
            include_str!("fixtures/provider-experiments/sqlite-copying/forwarding-chain.ash"),
        ),
        (
            "provider.ash",
            include_str!("fixtures/provider-experiments/sqlite-copying/provider.ash"),
        ),
        (
            "sqlite.ash",
            include_str!("fixtures/provider-experiments/sqlite-copying/sqlite.ash"),
        ),
    ] {
        fs::write(fixture.path(name), source).unwrap();
    }
    let (value, observations) = fixture.run("forwarding-chain.ash");
    assert_eq!(value, "Completed(Completed(Ok(42), Closed), Closed)");
    assert_closed_probe(&observations, 1);
    for operation in ["column_count", "column_type", "column_int64"] {
        assert_eq!(observations.calls(operation), 1, "{operation}");
    }
    for operation in ["finalize", "close"] {
        assert!(
            observations
                .events()
                .contains(&Event::Call { operation, code: 0 })
        );
    }
    assert_eq!(observations.calls("close_v2"), 0);
    assert_eq!(copied_sizes(&observations), (vec![], vec![]));
}
