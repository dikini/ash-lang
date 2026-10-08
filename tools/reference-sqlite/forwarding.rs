mod bridge;
use bridge::*;

fn read_first<S: StatementOps>(stmt: &S) -> Result<i64> { read_empty(stmt) }
fn read_empty<S: StatementOps>(stmt: &S) -> Result<i64> { read_null(stmt) }
fn read_null<S: StatementOps>(stmt: &S) -> Result<i64> { finish_copy(stmt) }
fn finish_copy<S: StatementOps>(stmt: &S) -> Result<i64> { stmt.column_int(0) }
fn main() -> Result<()> {
    let observations = log();
    let reports = with_connection(":memory:", &observations, |db| {
        with_statement(db, SqlText("SELECT 42"), |stmt| match stmt.step()? {
            Step::Row => read_first(stmt),
            Step::Done => Err(Error::MissingRow),
        })
    });
    let statement_report = closed(reports)?;
    assert_eq!(closed(statement_report)??, 42);
    assert_finished(&observations, 1, 1);
    // The actual forwarding fixture finalizes directly from its first row.
    assert_calls(&observations, &[("step", 1), ("column_count", 1), ("column_type", 1), ("column_int64", 1)]);
    assert!(observations.borrow().input_copies.is_empty());
    assert!(observations.borrow().output_copies.is_empty());
    println!("sqlite forwarding reference passed");
    Ok(())
}
