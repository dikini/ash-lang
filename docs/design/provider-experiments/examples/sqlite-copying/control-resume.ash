import provider as Provider
import sqlite as Sqlite

type CopiedRow = CopiedRow(Sqlite.TextOrNull, Sqlite.BytesOrNull)
effect Pause {
    pause : Unit -> Unit
}

main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<CopiedRow>>>
main () = handle (resource Sqlite.Connection<C> db = Sqlite.InMemory {
    resource Sqlite.Statement<S> stmt = (db, Sqlite.SqlText "SELECT 'héllo 世界', x'00ff'") {
        let ignored = perform Pause.pause ()
        read_row stmt
    }
}) with Pause {
    pause ignored => resume ()
}

read_row<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<CopiedRow> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
read_row stmt = match Sqlite.step stmt {
    Sqlite.Row => copy_columns stmt
    Sqlite.Done => Sqlite.Err Sqlite.MissingRow
    Sqlite.StepError(error) => Sqlite.Err error
}

copy_columns<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<CopiedRow> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
copy_columns stmt = match Sqlite.column_text (stmt, 0) {
    Sqlite.Err(error) => Sqlite.Err error
    Sqlite.Ok(text) => match Sqlite.column_bytes (stmt, 1) {
        Sqlite.Err(error) => Sqlite.Err error
        Sqlite.Ok(bytes) => finish_row (stmt, CopiedRow(text, bytes))
    }
}

finish_row<S, C> : (Sqlite.Statement<S, C>, CopiedRow) -> Sqlite.Result<CopiedRow> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
finish_row (stmt, copied) = match Sqlite.step stmt {
    Sqlite.Done => Sqlite.Ok copied
    Sqlite.Row => Sqlite.Err Sqlite.UnexpectedRow
    Sqlite.StepError(error) => Sqlite.Err error
}
