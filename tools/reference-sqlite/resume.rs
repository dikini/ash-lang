mod bridge;
use bridge::{BytesOrNull::*, TextOrNull::*, *};

#[derive(Debug, PartialEq, Eq)]
struct CopiedRow(TextOrNull, BytesOrNull);
fn read_row<S: StatementOps>(stmt: &mut S) -> Result<CopiedRow> {
    match stmt.step()? {
        Step::Done => Err(Error::MissingRow),
        Step::Row => {
            let copied = CopiedRow(stmt.column_text(0)?, stmt.column_bytes(1)?);
            expect_done(stmt)?;
            Ok(copied)
        }
    }
}
fn pause<T>(continuation: impl FnOnce() -> T) -> T {
    // Operational approximation only: Rust does not capture an Ash effect stack.
    continuation()
}
fn main() -> Result<()> {
    let observations = log();
    let reports = with_connection(":memory:", &observations, |db| {
        with_statement(db, SqlText("SELECT 'héllo 世界', x'00ff'"), |stmt| {
            pause(move || read_row(stmt))
        })
    });
    let statement_report = closed(reports)?;
    assert_eq!(closed(statement_report)??, CopiedRow(TextValue("héllo 世界".into()), BlobBytes(vec![0, 255])));
    assert_finished(&observations, 1, 1);
    assert_calls(&observations, &[("step", 2), ("column_text", 1), ("column_blob", 1)]);
    assert!(observations.borrow().input_copies.is_empty());
    assert_eq!(observations.borrow().output_copies, [13, 2]);
    println!("sqlite resume approximation passed");
    Ok(())
}
