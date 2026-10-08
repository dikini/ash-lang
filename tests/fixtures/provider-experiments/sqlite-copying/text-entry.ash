import provider as Provider
import sqlite as Sqlite
main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Sqlite.TextOrNull>>>
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {
resource Sqlite.Statement<S> stmt = (db, Sqlite.SqlText "SELECT ?1") {
match Sqlite.bind_text (stmt, 1, Sqlite.TextValue "héllo 世界") {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(()) => match Sqlite.step stmt {
Sqlite.Row => Sqlite.column_text (stmt, 0)
Sqlite.Done => Sqlite.Err Sqlite.MissingRow
Sqlite.StepError(error) => Sqlite.Err error
}
}
}
}
