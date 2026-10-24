import @builtin.foreign as Foreign
import producer as SQLite

main : Unit -> Foreign.CheckedScope<Foreign.CheckedScope<Int, SQLite.PrepareError, SQLite.FinalizeError>, SQLite.InitError, SQLite.CloseError>
main () = foreign host H {
    resource SQLite.Connection<H, C> connection = ":memory:" {
        resource SQLite.Statement<H, C, S> statement = (connection, "SELECT 1; ") {
            SQLite.prepared_status statement
        }
    }
}
