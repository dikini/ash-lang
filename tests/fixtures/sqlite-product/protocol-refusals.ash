import @ffi.sqlite as Sqlite
import @builtin.bytes as B

type Refusals = Refusals(Sqlite.Result<Int>, (Sqlite.Result<Int>, Sqlite.Result<Int>, Sqlite.Result<Int>, Sqlite.Result<Int>), (Sqlite.Result<Unit>, Sqlite.Result<Unit>, Sqlite.Result<Unit>, Sqlite.Result<Unit>), (Sqlite.StepResult, Sqlite.StepResult, Sqlite.StepResult))
main : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Refusals>> ! {Sqlite.Initialize}
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {
    resource Sqlite.Statement<S, C> stmt = (db, "SELECT 42, 'text', 1.5") {
        let before = Sqlite.column_int (stmt, 0)
        let row = Sqlite.step stmt
        let text = Sqlite.column_int (stmt, 1)
        let float = Sqlite.column_int (stmt, 2)
        let outside = Sqlite.column_int (stmt, 3)
        let oversized = Sqlite.column_int (stmt, (999999999999999 * 1000000000000000) + 999999999999999)
        let integer = Sqlite.bind_int (stmt, 1, 42)
        let text_bind = Sqlite.bind_text (stmt, 1, Sqlite.TextValue "valid")
        let blob = Sqlite.bind_bytes (stmt, 1, Sqlite.BlobBytes (B.empty ()))
        let clear = Sqlite.clear_bindings stmt
        let done = Sqlite.step stmt
        let after = Sqlite.step stmt
        Refusals(before, (text, float, outside, oversized), (integer, text_bind, blob, clear), (row, done, after))
    }
}
