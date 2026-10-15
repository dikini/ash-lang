import @ffi.sqlite as Sqlite

main : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, (Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Unit>>, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Unit>>, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, (Sqlite.Result<Unit>, Sqlite.Error)>)> ! {Sqlite.Initialize}
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {
    let create = resource Sqlite.Statement<T, C> stmt = (db, "CREATE TABLE t(id INTEGER UNIQUE)") {
        step_result (Sqlite.step stmt)
    }
    let first = resource Sqlite.Statement<I, C> stmt = (db, "INSERT INTO t VALUES (1)") {
        step_result (Sqlite.step stmt)
    }
    let duplicate = resource Sqlite.Statement<D, C> stmt = (db, "INSERT INTO t VALUES (1)") {
        let failed = step_result (Sqlite.step stmt)
        let diagnostic = Sqlite.diagnostic db
        (failed, diagnostic)
    }
    (create, first, duplicate)
}

step_result : Sqlite.StepResult -> Sqlite.Result<Unit>
step_result result = match result {
    Sqlite.Done => Sqlite.Ok ()
    Sqlite.Row => Sqlite.Err Sqlite.UnexpectedRow
    Sqlite.StepError(error) => Sqlite.Err error
}
