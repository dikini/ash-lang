import @builtin.foreign as Foreign
import producer as SQLite

main : Unit -> Foreign.CheckedScope<Foreign.CheckedScope<Int, SQLite.PrepareError, SQLite.FinalizeError>, SQLite.InitError, SQLite.CloseError>
main () = foreign host H {
    match perform SQLite.Initialize<H>.call () {
        Foreign.CheckedReturned(status) => match status == 0 {
            true => resource SQLite.Connection<H, C> connection = ":memory:" {
                resource SQLite.Statement<H, C, S> statement = (connection, "SELECT 1; ") {
                    SQLite.prepared_status statement
                }
            }
            false => Foreign.CheckedNotAcquired (SQLite.NativeOpenError status)
        }
        Foreign.CheckedConversionFailed(error) => Foreign.CheckedNotAcquired (SQLite.OpenConversion error)
        Foreign.BoundaryFailed(reason) => Foreign.CheckedNotAcquired (SQLite.OpenBoundary reason)
    }
}
