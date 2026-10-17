import @ffi.sqlite as Sqlite

main : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, (Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Int>>, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Unit>>, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, (Sqlite.Result<Unit>, Sqlite.Error)>)> ! {Sqlite.Initialize}
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {
    let negative = resource Sqlite.Statement<N, C> stmt = (db, "SELECT -1") {
        match Sqlite.step stmt {
            Sqlite.Row => Sqlite.column_int (stmt, 0)
            Sqlite.Done => Sqlite.Err Sqlite.MissingRow
            Sqlite.StepError(error) => Sqlite.Err error
        }
    }
    let refused = match negative {
        Sqlite.Completed(Sqlite.Ok(index), Sqlite.Closed) => resource Sqlite.Statement<B, C> stmt = (db, "SELECT ?1") {
            Sqlite.bind_int (stmt, index, 42)
        }
        _ => Sqlite.NotAcquired Sqlite.InvalidSql
    }
    let range = resource Sqlite.Statement<R, C> stmt = (db, "SELECT ?1") {
        let status = Sqlite.bind_int (stmt, 2, 42)
        let diagnostic = Sqlite.diagnostic db
        (status, diagnostic)
    }
    (negative, refused, range)
}
