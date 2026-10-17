import @ffi.sqlite as Sqlite
main : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<(Sqlite.TextOrNull, Sqlite.TextOrNull, Sqlite.TextOrNull)>>> ! {Sqlite.Initialize}
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {
    resource Sqlite.Statement<S, C> stmt = (db, "SELECT ?1") {
        match Sqlite.bind_text (stmt, 1, Sqlite.TextValue "héllo 世界") {
            Sqlite.Err(error) => Sqlite.Err error
            Sqlite.Ok(()) => match read_text stmt {
                Sqlite.Err(error) => Sqlite.Err error
                Sqlite.Ok(first) => after_first (stmt, first)
            }
        }
    }
}
read_text<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Sqlite.TextOrNull> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
read_text stmt = match Sqlite.step stmt {
    Sqlite.Row => Sqlite.column_text (stmt, 0)
    Sqlite.Done => Sqlite.Err Sqlite.MissingRow
    Sqlite.StepError(error) => Sqlite.Err error
}
after_first<S, C> : (Sqlite.Statement<S, C>, Sqlite.TextOrNull) -> Sqlite.Result<(Sqlite.TextOrNull, Sqlite.TextOrNull, Sqlite.TextOrNull)> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
after_first (stmt, first) = match Sqlite.reset stmt {
    Sqlite.Err(error) => Sqlite.Err error
    Sqlite.Ok(()) => match read_text stmt {
        Sqlite.Err(error) => Sqlite.Err error
        Sqlite.Ok(second) => after_second (stmt, first, second)
    }
}
after_second<S, C> : (Sqlite.Statement<S, C>, Sqlite.TextOrNull, Sqlite.TextOrNull) -> Sqlite.Result<(Sqlite.TextOrNull, Sqlite.TextOrNull, Sqlite.TextOrNull)> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
after_second (stmt, first, second) = match Sqlite.reset stmt {
    Sqlite.Err(error) => Sqlite.Err error
    Sqlite.Ok(()) => match Sqlite.clear_bindings stmt {
        Sqlite.Err(error) => Sqlite.Err error
        Sqlite.Ok(()) => read_cleared (stmt, first, second)
    }
}
read_cleared<S, C> : (Sqlite.Statement<S, C>, Sqlite.TextOrNull, Sqlite.TextOrNull) -> Sqlite.Result<(Sqlite.TextOrNull, Sqlite.TextOrNull, Sqlite.TextOrNull)> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
read_cleared (stmt, first, second) = match read_text stmt {
    Sqlite.Err(error) => Sqlite.Err error
    Sqlite.Ok(cleared) => match Sqlite.step stmt {
        Sqlite.Done => Sqlite.Ok (first, second, cleared)
        Sqlite.Row => Sqlite.Err Sqlite.UnexpectedRow
        Sqlite.StepError(error) => Sqlite.Err error
    }
}
