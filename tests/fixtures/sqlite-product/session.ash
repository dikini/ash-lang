import @ffi.sqlite as Sqlite
import rows as Rows
import @builtin.bytes as B

type Stored = Stored(Int, Sqlite.TextOrNull, Sqlite.BytesOrNull)
type SessionOutcome = ByteRefused
    | SessionReports(Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, (Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Unit>>, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Unit>>, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Unit>>, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Unit>>, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Rows.List<Stored>>>)>, Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Rows.List<Stored>>>>)

main : Unit -> SessionOutcome ! {Sqlite.Initialize}
main () = match make_blob () {
    B.InvalidByte => ByteRefused
    B.BytesAppended(bytes) => {
        let first = resource Sqlite.Connection<C> db = (Sqlite.File "__SQLITE_FILE__") {
            let create = resource Sqlite.Statement<Create, C> stmt = (db, "CREATE TABLE sample (id INTEGER, text_value TEXT, blob_value BLOB)") {
                expect_done stmt
            }
            let begin = resource Sqlite.Statement<Begin, C> stmt = (db, "BEGIN") {
                expect_done stmt
            }
            let inserted = resource Sqlite.Statement<S, C> stmt = (db, "INSERT INTO sample VALUES (?1, ?2, ?3)") {
                insert_three (stmt, bytes)
            }
            let commit = resource Sqlite.Statement<Commit, C> stmt = (db, "COMMIT") {
                expect_done stmt
            }
            let query = resource Sqlite.Statement<Q, C> stmt = (db, "SELECT id, text_value, blob_value FROM sample ORDER BY id") {
                Rows.collect (stmt, read_stored)
            }
            (create, begin, inserted, commit, query)
        }
        let reopened = resource Sqlite.Connection<D> db = (Sqlite.File "__SQLITE_FILE__") {
            resource Sqlite.Statement<Q, D> stmt = (db, "SELECT id, text_value, blob_value FROM sample ORDER BY id") {
                Rows.collect (stmt, read_stored)
            }
        }
        SessionReports(first, reopened)
    }
}

make_blob : Unit -> B.AppendResult
make_blob () = match B.append_byte (B.empty (), 0) {
    B.BytesAppended(zero) => B.append_byte (zero, 255)
    B.InvalidByte => B.InvalidByte
}

expect_done<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Unit> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
expect_done stmt = match Sqlite.step stmt {
    Sqlite.Done => Sqlite.Ok ()
    Sqlite.Row => Sqlite.Err Sqlite.UnexpectedRow
    Sqlite.StepError(error) => Sqlite.Err error
}

insert_three<S, C> : (Sqlite.Statement<S, C>, Bytes) -> Sqlite.Result<Unit> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
insert_three (stmt, bytes) = match first_record (stmt, bytes) {
    Sqlite.Err(error) => Sqlite.Err error
    Sqlite.Ok(()) => match second_record stmt {
        Sqlite.Err(error) => Sqlite.Err error
        Sqlite.Ok(()) => third_record stmt
    }
}

first_record<S, C> : (Sqlite.Statement<S, C>, Bytes) -> Sqlite.Result<Unit> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
first_record (stmt, bytes) = match Sqlite.bind_int (stmt, 1, 1) {
    Sqlite.Ok(()) => match Sqlite.bind_text (stmt, 2, Sqlite.TextValue "héllo 世界") {
        Sqlite.Ok(()) => match Sqlite.bind_bytes (stmt, 3, Sqlite.BlobBytes bytes) {
            Sqlite.Ok(()) => expect_done stmt
            Sqlite.Err(error) => Sqlite.Err error
        }
        Sqlite.Err(error) => Sqlite.Err error
    }
    Sqlite.Err(error) => Sqlite.Err error
}

second_record<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Unit> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
second_record stmt = match Sqlite.reset stmt {
    Sqlite.Ok(()) => match Sqlite.bind_int (stmt, 1, 2) {
        Sqlite.Ok(()) => expect_done stmt
        Sqlite.Err(error) => Sqlite.Err error
    }
    Sqlite.Err(error) => Sqlite.Err error
}

third_record<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Unit> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
third_record stmt = match Sqlite.reset stmt {
    Sqlite.Ok(()) => match Sqlite.clear_bindings stmt {
        Sqlite.Ok(()) => bind_third stmt
        Sqlite.Err(error) => Sqlite.Err error
    }
    Sqlite.Err(error) => Sqlite.Err error
}

bind_third<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Unit> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
bind_third stmt = match Sqlite.bind_int (stmt, 1, 3) {
    Sqlite.Ok(()) => match Sqlite.bind_text (stmt, 2, Sqlite.TextValue "third") {
        Sqlite.Ok(()) => match Sqlite.bind_bytes (stmt, 3, Sqlite.BlobBytes (B.empty ())) {
            Sqlite.Ok(()) => expect_done stmt
            Sqlite.Err(error) => Sqlite.Err error
        }
        Sqlite.Err(error) => Sqlite.Err error
    }
    Sqlite.Err(error) => Sqlite.Err error
}

read_stored<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Stored> ! {Sqlite.StatementOps<Sqlite.Statement<S, C>>} where Sqlite.StatementProvider<Sqlite.Statement<S, C>>
read_stored stmt = match Sqlite.column_int (stmt, 0) {
    Sqlite.Ok(integer) => match Sqlite.column_text (stmt, 1) {
        Sqlite.Ok(text) => match Sqlite.column_bytes (stmt, 2) {
            Sqlite.Ok(bytes) => Sqlite.Ok (Stored(integer, text, bytes))
            Sqlite.Err(error) => Sqlite.Err error
        }
        Sqlite.Err(error) => Sqlite.Err error
    }
    Sqlite.Err(error) => Sqlite.Err error
}
