import @ffi.sqlite as Sqlite

pub type List<T> = Nil
    | Cons(T, List<T>)

pub collect<S, C, T> : (Sqlite.Statement<S, C>, Sqlite.Statement<S, C> -> Sqlite.Result<T> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>}) -> Sqlite.Result<List<T>> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
collect (stmt, read) = match Sqlite.step stmt {
    Sqlite.Done => Sqlite.Ok Nil
    Sqlite.StepError(error) => Sqlite.Err error
    Sqlite.Row => match read stmt {
        Sqlite.Err(error) => Sqlite.Err error
        Sqlite.Ok(value) => match collect (stmt, read) {
            Sqlite.Err(error) => Sqlite.Err error
            Sqlite.Ok(rest) => Sqlite.Ok (Cons(value, rest))
        }
    }
}
