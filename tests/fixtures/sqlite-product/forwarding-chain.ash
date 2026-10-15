import @ffi.sqlite as Sqlite

main : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Int>>> ! {Sqlite.Initialize}
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {
    resource Sqlite.Statement<S, C> stmt = (db, "SELECT 42") {
        match Sqlite.step stmt {
            Sqlite.Row => read_first stmt
            Sqlite.Done => Sqlite.Err Sqlite.MissingRow
            Sqlite.StepError(error) => Sqlite.Err error
        }
    }
}

read_first<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Int> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
read_first stmt = read_empty stmt

read_empty<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Int> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
read_empty stmt = read_null stmt

read_null<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Int> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
read_null stmt = finish_copy stmt

finish_copy<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Int> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
finish_copy stmt = Sqlite.column_int (stmt, 0)
