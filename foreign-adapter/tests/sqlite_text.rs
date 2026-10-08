//! Native copying, strict TEXT conversion and column admission evidence.

use ash_foreign_adapter::{Column, Connection, Error, Event, Observations, Statement, Step};

fn statement(db: &mut Connection, sql: &str) -> Statement {
    db.prepare(sql).unwrap().expect("executable SQL")
}

#[test]
fn copied_utf8_text_survives_input_reset_and_owner_completion() {
    let observations = Observations::default();
    let mut db = Connection::open_observed(":memory:", observations.clone()).unwrap();
    let mut stmt = statement(&mut db, "SELECT ?1");
    {
        let input = String::from("Здравей 🦀");
        stmt.bind_text_copy(1, &input).unwrap();
    }
    assert_eq!(stmt.step(), Ok(Step::Row));
    let copied = stmt.column_copy(0).unwrap();
    stmt.reset().unwrap();
    assert_eq!(stmt.step(), Ok(Step::Row));
    assert_eq!(stmt.column_copy(0), Ok(copied.clone()));
    stmt.reset().unwrap();
    stmt.clear_bindings().unwrap();
    assert_eq!(stmt.step(), Ok(Step::Row));
    assert_eq!(stmt.column_copy(0), Ok(Column::Null));
    stmt.finalize().unwrap();
    db.close().unwrap();
    assert_eq!(copied, Column::Text("Здравей 🦀".into()));
    assert_eq!(observations.calls("bind_text_copy"), 1);
    assert_eq!(observations.calls("column_text"), 2);
    assert!(
        observations
            .events()
            .contains(&Event::InputCopied("Здравей 🦀".len()))
    );
    assert!(
        observations
            .events()
            .contains(&Event::OutputCopied("Здравей 🦀".len()))
    );
}

#[test]
fn empty_text_empty_blob_and_null_remain_distinct() {
    let mut db = Connection::open(":memory:").unwrap();
    let mut stmt = statement(&mut db, "SELECT ?1, ?2, ?3");
    stmt.bind_text_copy(1, "").unwrap();
    stmt.bind_blob_copy(2, &[]).unwrap();
    stmt.bind_null(3).unwrap();
    assert_eq!(stmt.step(), Ok(Step::Row));
    assert_eq!(stmt.column_copy(0), Ok(Column::Text(String::new())));
    assert_eq!(stmt.column_copy(1), Ok(Column::Blob(Vec::new())));
    assert_eq!(stmt.column_copy(2), Ok(Column::Null));
}

#[test]
fn native_text_preserves_embedded_nul_and_rejects_invalid_utf8() {
    let observations = Observations::default();
    let mut db = Connection::open_observed(":memory:", observations.clone()).unwrap();
    let mut stmt = statement(
        &mut db,
        "SELECT CAST(x'610062' AS TEXT), CAST(x'ff' AS TEXT), 1.5",
    );
    assert_eq!(stmt.step(), Ok(Step::Row));
    assert_eq!(stmt.column_copy(0), Ok(Column::Text("a\0b".into())));
    assert_eq!(stmt.column_copy(1), Err(Error::InvalidUtf8));
    assert_eq!(stmt.column_copy(2), Err(Error::ColumnKind));
    assert!(observations.events().contains(&Event::OutputCopied(3)));
}

#[test]
fn text_nul_and_protocol_errors_prevent_native_bind() {
    let observations = Observations::default();
    let mut db = Connection::open_observed(":memory:", observations.clone()).unwrap();
    let mut stmt = statement(&mut db, "SELECT ?1");
    assert!(matches!(
        stmt.bind_text_copy(1, "a\0b"),
        Err(Error::InvalidInput(_))
    ));
    assert!(matches!(
        stmt.bind_text_copy(0, "x"),
        Err(Error::InvalidInput(_))
    ));
    assert!(matches!(
        stmt.bind_text_copy(usize::MAX, "x"),
        Err(Error::InvalidInput(_))
    ));
    assert_eq!(observations.calls("bind_text_copy"), 0);
    stmt.bind_text_copy(1, "x").unwrap();
    assert_eq!(stmt.step(), Ok(Step::Row));
    assert!(matches!(
        stmt.bind_text_copy(1, "y"),
        Err(Error::Protocol(_))
    ));
    assert_eq!(observations.calls("bind_text_copy"), 1);
}

#[test]
fn utf8_path_sql_and_text_persist_after_close_and_reopen() {
    let path = std::env::temp_dir().join(format!("ash-text-{}-данни.sqlite", std::process::id()));
    let path_text = path.to_str().unwrap();
    let mut db = Connection::open(path_text).unwrap();
    let mut create = statement(&mut db, "CREATE TABLE \"данни\"(value TEXT)");
    assert_eq!(create.step(), Ok(Step::Done));
    create.finalize().unwrap();
    let mut insert = statement(&mut db, "INSERT INTO \"данни\" VALUES (?1)");
    insert.bind_text_copy(1, "памет 🦀").unwrap();
    assert_eq!(insert.step(), Ok(Step::Done));
    insert.finalize().unwrap();
    db.close().unwrap();
    let mut reopened = Connection::open(path_text).unwrap();
    let mut query = statement(&mut reopened, "SELECT value FROM \"данни\"");
    assert_eq!(query.step(), Ok(Step::Row));
    assert_eq!(query.column_copy(0), Ok(Column::Text("памет 🦀".into())));
    query.finalize().unwrap();
    reopened.close().unwrap();
    std::fs::remove_file(path).unwrap();
}

#[test]
fn typed_input_and_protocol_failures_preserve_the_rejection_cause() {
    use ash_foreign_adapter::{InputError, ProtocolError};
    let observations = Observations::default();
    assert!(matches!(
        Connection::open_observed("a\0b", observations.clone()),
        Err(Error::InvalidInput(InputError::PathContainsNul))
    ));
    assert_eq!(observations.calls("open"), 0);
    let mut db = Connection::open_observed(":memory:", observations.clone()).unwrap();
    assert!(matches!(
        db.prepare("SELECT\0 1"),
        Err(Error::InvalidInput(InputError::SqlContainsNul))
    ));
    let mut stmt = statement(&mut db, "SELECT ?1");
    assert_eq!(
        stmt.bind_text_copy(1, "a\0b"),
        Err(Error::InvalidInput(InputError::TextContainsNul))
    );
    assert_eq!(
        stmt.bind_int64(0, 1),
        Err(Error::InvalidInput(InputError::ParameterIndexZero))
    );
    assert_eq!(
        stmt.bind_int64(usize::MAX, 1),
        Err(Error::InvalidInput(InputError::ParameterIndexRange))
    );
    assert_eq!(
        stmt.column_copy(0),
        Err(Error::Protocol(ProtocolError::ColumnRequiresRow))
    );
    assert_eq!(stmt.step(), Ok(Step::Row));
    assert_eq!(
        stmt.bind_null(1),
        Err(Error::Protocol(ProtocolError::BindingRequiresPrepared))
    );
    assert_eq!(
        stmt.column_copy(usize::MAX),
        Err(Error::InvalidInput(InputError::ColumnIndexRange))
    );
    assert_eq!(
        stmt.column_copy(1),
        Err(Error::InvalidInput(InputError::ColumnOutsideRow))
    );
    assert_eq!(stmt.step(), Ok(Step::Done));
    assert_eq!(
        stmt.step(),
        Err(Error::Protocol(ProtocolError::StepRequiresPreparedOrRow))
    );
    stmt.finalize().unwrap();
    db.close().unwrap();
    assert_eq!(
        db.diagnostic(),
        Err(Error::Protocol(ProtocolError::ConnectionClosed))
    );
}

#[test]
fn bounded_column_copy_refuses_before_independent_storage_is_published() {
    let observations = Observations::default();
    let mut db = Connection::open_observed(":memory:", observations.clone()).unwrap();
    let mut stmt = statement(&mut db, "SELECT zeroblob(5), 'é世界'");
    assert_eq!(stmt.step(), Ok(Step::Row));
    assert_eq!(
        stmt.column_copy_bounded(0, 4),
        Err(Error::CopyWorkExhausted {
            requested: 5,
            available: 4
        })
    );
    assert_eq!(
        stmt.column_copy_bounded(1, 7),
        Err(Error::CopyWorkExhausted {
            requested: 8,
            available: 7
        })
    );
    assert!(
        !observations
            .events()
            .iter()
            .any(|event| matches!(event, Event::OutputCopied(_)))
    );
    assert_eq!(stmt.column_copy_bounded(0, 5), Ok(Column::Blob(vec![0; 5])));
    assert_eq!(
        stmt.column_copy_bounded(1, 8),
        Ok(Column::Text("é世界".into()))
    );
    stmt.finalize().unwrap();
    db.close().unwrap();
    assert_eq!(observations.calls("finalize"), 1);
    assert_eq!(observations.calls("close"), 1);
}

#[test]
fn zero_copy_limit_admits_empty_values_and_null() {
    let mut db = Connection::open(":memory:").unwrap();
    let mut stmt = statement(&mut db, "SELECT zeroblob(0), '', NULL");
    assert_eq!(stmt.step(), Ok(Step::Row));
    assert_eq!(stmt.column_copy_bounded(0, 0), Ok(Column::Blob(Vec::new())));
    assert_eq!(
        stmt.column_copy_bounded(1, 0),
        Ok(Column::Text(String::new()))
    );
    assert_eq!(stmt.column_copy_bounded(2, 0), Ok(Column::Null));
}

#[test]
fn typed_column_rejects_invalid_utf8_text_before_conversion_or_copy() {
    use ash_foreign_adapter::CopyColumnKind;
    let observations = Observations::default();
    let mut db = Connection::open_observed(":memory:", observations.clone()).unwrap();
    let mut stmt = statement(&mut db, "SELECT CAST(x'ff' AS TEXT), hex(zeroblob(32))");
    assert_eq!(stmt.step(), Ok(Step::Row));
    assert_eq!(
        stmt.column_copy_kind_bounded(0, CopyColumnKind::Integer, 0),
        Err(Error::ColumnKind)
    );
    assert_eq!(
        stmt.column_copy_kind_bounded(1, CopyColumnKind::BlobOrNull, 0),
        Err(Error::ColumnKind)
    );
    assert_eq!(observations.calls("column_count"), 2);
    assert_eq!(observations.calls("column_type"), 2);
    assert_eq!(observations.calls("column_text"), 0);
    assert_eq!(observations.calls("column_blob"), 0);
    assert_eq!(observations.calls("column_bytes"), 0);
    assert!(
        !observations
            .events()
            .iter()
            .any(|event| matches!(event, Event::OutputCopied(_)))
    );
    assert_eq!(
        stmt.column_copy_kind_bounded(0, CopyColumnKind::TextOrNull, 1),
        Err(Error::InvalidUtf8)
    );
    stmt.finalize().unwrap();
    db.close().unwrap();
}

#[test]
fn typed_column_nullable_kinds_and_integer_kind_remain_distinct() {
    use ash_foreign_adapter::CopyColumnKind;
    let observations = Observations::default();
    let mut db = Connection::open_observed(":memory:", observations.clone()).unwrap();
    let mut stmt = statement(&mut db, "SELECT NULL, 42, 'text', x'01', 1.5");
    assert_eq!(stmt.step(), Ok(Step::Row));
    assert_eq!(
        stmt.column_copy_kind_bounded(0, CopyColumnKind::Integer, 0),
        Err(Error::ColumnKind)
    );
    assert_eq!(
        stmt.column_copy_kind_bounded(0, CopyColumnKind::TextOrNull, 0),
        Ok(Column::Null)
    );
    assert_eq!(
        stmt.column_copy_kind_bounded(0, CopyColumnKind::BlobOrNull, 0),
        Ok(Column::Null)
    );
    assert_eq!(
        stmt.column_copy_kind_bounded(1, CopyColumnKind::Integer, 0),
        Ok(Column::Integer(42))
    );
    for (column, expected) in [
        (1, CopyColumnKind::TextOrNull),
        (2, CopyColumnKind::BlobOrNull),
        (3, CopyColumnKind::TextOrNull),
        (4, CopyColumnKind::Integer),
    ] {
        assert_eq!(
            stmt.column_copy_kind_bounded(column, expected, 0),
            Err(Error::ColumnKind)
        );
    }
    assert_eq!(observations.calls("column_count"), 8);
    assert_eq!(observations.calls("column_type"), 8);
    assert_eq!(observations.calls("column_int64"), 1);
    assert_eq!(observations.calls("column_text"), 0);
    assert_eq!(observations.calls("column_blob"), 0);
}

#[test]
fn native_guard_drop_does_not_report_binding_finish_dispatch() {
    let observations = Observations::default();
    {
        let mut db = Connection::open_observed(":memory:", observations.clone()).unwrap();
        let _stmt = statement(&mut db, "SELECT 1");
    }
    assert_eq!(observations.calls("finalize"), 1);
    assert_eq!(observations.calls("close"), 1);
    assert!(
        !observations
            .events()
            .iter()
            .any(|event| matches!(event, Event::FinishDispatched { .. }))
    );
}
