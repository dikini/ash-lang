mod bridge;
use bridge::{BytesOrNull::*, TextOrNull::*, *};
use std::{fs, path::PathBuf, time::{SystemTime, UNIX_EPOCH}};

#[derive(Debug, PartialEq, Eq)]
struct Stored(i64, TextOrNull, BytesOrNull);
fn run_sql(db: &Connection, sql: &str) -> Report<Result<()>> {
    with_statement(db, SqlText(sql), |stmt| expect_done(stmt))
}
fn insert_three<S: StatementOps>(stmt: &mut S, bytes: Vec<u8>) -> Result<()> {
    stmt.bind_int(1, 1)?;
    stmt.bind_text(2, &TextValue("héllo 世界".into()))?;
    stmt.bind_bytes(3, &BlobBytes(bytes))?;
    expect_done(stmt)?;
    stmt.reset()?;
    // Reset keeps the first row's copied text/blob bindings.
    stmt.bind_int(1, 2)?;
    expect_done(stmt)?;
    stmt.reset()?;
    stmt.clear_bindings()?;
    stmt.bind_int(1, 3)?;
    stmt.bind_text(2, &TextValue("third".into()))?;
    stmt.bind_bytes(3, &BlobBytes(Vec::new()))?;
    expect_done(stmt)
}
fn read_stored<S: StatementOps>(stmt: &S) -> Result<Stored> {
    Ok(Stored(stmt.column_int(0)?, stmt.column_text(1)?, stmt.column_bytes(2)?))
}
fn query(db: &Connection) -> Report<Result<List<Stored>>> {
    with_statement(db, SqlText("SELECT id, text_value, blob_value FROM sample ORDER BY id"), |stmt| {
        collect(stmt, &mut |row| read_stored(row))
    })
}
struct TempDirectory(PathBuf);
impl Drop for TempDirectory { fn drop(&mut self) { let _ = fs::remove_dir_all(&self.0); } }
fn expected_rows() -> List<Stored> {
    List::Cons(Stored(1, TextValue("héllo 世界".into()), BlobBytes(vec![0, 255])), Box::new(
        List::Cons(Stored(2, TextValue("héllo 世界".into()), BlobBytes(vec![0, 255])), Box::new(
            List::Cons(Stored(3, TextValue("third".into()), BlobBytes(Vec::new())), Box::new(List::Nil))))))
}
fn main() -> Result<()> {
    let stamp = SystemTime::now().duration_since(UNIX_EPOCH).map_err(|_| Error::Protocol)?.as_nanos();
    let directory = std::env::temp_dir().join(format!("rust-sqlite-reference-{}-{stamp}", std::process::id()));
    fs::create_dir(&directory)?;
    let directory = TempDirectory(directory);
    let path = directory.0.join("session.sqlite3");
    let path = path.to_str().ok_or(Error::BadText)?;
    let observations = log();
    let first = with_connection(path, &observations, |db| {
        let create = run_sql(db, "CREATE TABLE sample (id INTEGER, text_value TEXT, blob_value BLOB)");
        let begin = run_sql(db, "BEGIN");
        let inserted = with_statement(db, SqlText("INSERT INTO sample VALUES (?1, ?2, ?3)"), |stmt| {
            insert_three(stmt, vec![0, 255])
        });
        let commit = run_sql(db, "COMMIT");
        let queried = query(db);
        (create, begin, inserted, commit, queried)
    });
    let reopened = with_connection(path, &observations, query);
    let (create, begin, inserted, commit, queried) = closed(first)?;
    for unit in [create, begin, inserted, commit] { closed(unit)??; }
    assert_eq!(closed(queried)??, expected_rows());
    assert_eq!(closed(closed(reopened)?)??, expected_rows());
    assert_finished(&observations, 2, 6);
    assert_calls(&observations, &[("reset", 2), ("clear_bindings", 1), ("bind_int64", 3),
                                  ("bind_text_copy", 2), ("bind_blob_copy", 2), ("step", 14),
                                  ("column_int64", 6), ("column_text", 6), ("column_blob", 6)]);
    assert_eq!(observations.borrow().input_copies, [13, 2, 5, 0]);
    assert_eq!(observations.borrow().output_copies, [13, 2, 13, 2, 5, 0, 13, 2, 13, 2, 5, 0]);
    println!("sqlite persistence reference passed");
    Ok(())
}
