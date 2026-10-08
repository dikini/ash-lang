import provider as Provider
import sqlite as Sqlite

main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Int>>>
main () = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {
resource Sqlite.Statement<S> stmt = (db, (Sqlite.select_parameter ())) {
match Sqlite.bind_int (stmt, 1, 42) {
Sqlite.Ok(()) => match Sqlite.step stmt {
Sqlite.Row => match Sqlite.column_int (stmt, 0) {
Sqlite.Ok(value) => match Sqlite.step stmt {
Sqlite.Done => Sqlite.Ok value
Sqlite.Row => Sqlite.Err Sqlite.UnexpectedRow
Sqlite.StepError(error) => Sqlite.Err error
}
Sqlite.Err(error) => Sqlite.Err error
}
Sqlite.Done => Sqlite.Err Sqlite.MissingRow
Sqlite.StepError(error) => Sqlite.Err error
}
Sqlite.Err(error) => Sqlite.Err error
}
}
}
