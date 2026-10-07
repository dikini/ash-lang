import provider as Provider
import sqlite as Sqlite

main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Int>>>
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {
resource Sqlite.Statement<S> stmt = (db, Sqlite.SqlText "SELECT 42") {
match Sqlite.step stmt {
Sqlite.Row => read_first stmt
Sqlite.Done => Sqlite.Err Sqlite.MissingRow
Sqlite.StepError(error) => Sqlite.Err error
}
}
}

read_first<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Int> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
read_first stmt = read_empty stmt

read_empty<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Int> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
read_empty stmt = read_null stmt

read_null<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Int> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
read_null stmt = finish_copy stmt

finish_copy<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Int> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
finish_copy stmt = Sqlite.column_int (stmt, 0)
