mod bridge;
use bridge::{BytesOrNull::*, TextOrNull::*, *};

const QUERY: &str = "SELECT ?1, ?2, ?3, ?4, ?5, ?6, ?7, '世界' || char(0) || 'tail'";
#[derive(Debug, PartialEq, Eq)]
struct Copied(i64, TextOrNull, BytesOrNull, TextOrNull, BytesOrNull, TextOrNull, BytesOrNull, TextOrNull);

fn bind_first<S: StatementOps>(stmt: &mut S, bytes: Vec<u8>) -> Result<Copied> {
    stmt.bind_int(1, 42)?;
    stmt.bind_text(2, &TextValue("héllo 世界".into()))?;
    stmt.bind_bytes(3, &BlobBytes(bytes))?;
    bind_empty(stmt)
}
fn bind_empty<S: StatementOps>(stmt: &mut S) -> Result<Copied> {
    stmt.bind_text(4, &TextValue(String::new()))?;
    stmt.bind_bytes(5, &BlobBytes(Vec::new()))?;
    bind_null(stmt)
}
fn bind_null<S: StatementOps>(stmt: &mut S) -> Result<Copied> {
    stmt.bind_text(6, &NullText)?;
    stmt.bind_bytes(7, &NullBytes)?;
    match stmt.step()? { Step::Row => read_first(stmt), Step::Done => Err(Error::MissingRow) }
}
fn read_first<S: StatementOps>(stmt: &mut S) -> Result<Copied> {
    let integer = stmt.column_int(0)?;
    let text = stmt.column_text(1)?;
    let bytes = stmt.column_bytes(2)?;
    read_empty(stmt, integer, text, bytes)
}
fn read_empty<S: StatementOps>(stmt: &mut S, integer: i64, text: TextOrNull, bytes: BytesOrNull) -> Result<Copied> {
    let empty_text = stmt.column_text(3)?;
    let empty_bytes = stmt.column_bytes(4)?;
    read_null(stmt, integer, text, bytes, empty_text, empty_bytes)
}
fn read_null<S: StatementOps>(stmt: &mut S, integer: i64, text: TextOrNull, bytes: BytesOrNull,
                            empty_text: TextOrNull, empty_bytes: BytesOrNull) -> Result<Copied> {
    let value = Copied(integer, text, bytes, empty_text, empty_bytes,
                       stmt.column_text(5)?, stmt.column_bytes(6)?, stmt.column_text(7)?);
    expect_done(stmt)?;
    Ok(value)
}
fn main() -> Result<()> {
    let observations = log();
    let reports = with_connection(":memory:", &observations, |db| {
        with_statement(db, SqlText(QUERY), |stmt| {
            let value = bind_first(stmt, vec![0, 255])?;
            Ok::<_, Error>(move || value)
        })
    });
    let statement_report = closed(reports)?;
    let copied = closed(statement_report)??;
    // This closure retains only owned columns; both native scopes have completed.
    assert_eq!(copied(), Copied(42, TextValue("héllo 世界".into()), BlobBytes(vec![0, 255]),
                                TextValue(String::new()), BlobBytes(Vec::new()), NullText, NullBytes,
                                TextValue("世界\0tail".into())));
    assert_finished(&observations, 1, 1);
    assert_calls(&observations, &[("bind_int64", 1), ("bind_text_copy", 2), ("bind_blob_copy", 2),
                                  ("bind_null", 2), ("step", 2), ("column_int64", 1), ("column_text", 3), ("column_blob", 2)]);
    assert_eq!(observations.borrow().input_copies, [13, 2, 0, 0]);
    assert_eq!(observations.borrow().output_copies, [13, 2, 0, 0, 11]);
    println!("sqlite copying reference passed");
    Ok(())
}
