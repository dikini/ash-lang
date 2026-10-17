import @ffi.sqlite as Sqlite

main : Unit -> (Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Int>>>, Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Int>>>) ! {Sqlite.Initialize}
main () = (session (), session ())

session : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Int>>> ! {Sqlite.Initialize}
session () = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {
    resource Sqlite.Statement<S, C> stmt = (db, "SELECT ?1") {
        match Sqlite.bind_int (stmt, 1, 42) {
            Sqlite.Ok(()) => after_bind stmt
            Sqlite.Err(error) => Sqlite.Err error
        }
    }
}


after_bind<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Int> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
after_bind stmt = match Sqlite.step stmt {
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
