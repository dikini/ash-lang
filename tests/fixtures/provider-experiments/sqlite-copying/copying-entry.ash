import provider as Provider
import sqlite as Sqlite
import @builtin.bytes as B

pub type Copied = Copied(Int, Sqlite.TextOrNull, Sqlite.BytesOrNull, Sqlite.TextOrNull, Sqlite.BytesOrNull, Sqlite.TextOrNull, Sqlite.BytesOrNull, Sqlite.TextOrNull)
type CopyOutcome = ByteRefused
| CopySession(Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Copied>>>)

make_blob : Unit -> B.AppendResult
make_blob () = match B.append_byte (B.empty (), 0) {
B.BytesAppended(zero) => B.append_byte (zero, 255)
B.InvalidByte => B.InvalidByte
}

main : Unit -> CopyOutcome
main () = match make_blob () {
B.InvalidByte => ByteRefused
B.BytesAppended(bytes) => CopySession (resource Sqlite.Connection<C> db = Sqlite.InMemory {
resource Sqlite.Statement<S> stmt = (db, Sqlite.SqlText "SELECT ?1, ?2, ?3, ?4, ?5, ?6, ?7, '世界' || char(0) || 'tail'") {
bind_first (stmt, bytes)
}
})
}

bind_first<S, C> : (Sqlite.Statement<S, C>, Bytes) -> Sqlite.Result<Copied> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
bind_first (stmt, bytes) = match Sqlite.bind_int (stmt, 1, 42) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(()) => match Sqlite.bind_text (stmt, 2, Sqlite.TextValue "héllo 世界") {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(()) => match Sqlite.bind_bytes (stmt, 3, Sqlite.BlobBytes bytes) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(()) => bind_empty stmt
}
}
}

bind_empty<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Copied> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
bind_empty stmt = match Sqlite.bind_text (stmt, 4, Sqlite.TextValue "") {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(()) => match Sqlite.bind_bytes (stmt, 5, Sqlite.BlobBytes (B.empty ())) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(()) => bind_null stmt
}
}

bind_null<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Copied> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
bind_null stmt = match Sqlite.bind_text (stmt, 6, Sqlite.NullText) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(()) => match Sqlite.bind_bytes (stmt, 7, Sqlite.NullBytes) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(()) => read_copy stmt
}
}

read_copy<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Copied> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
read_copy stmt = match Sqlite.step stmt {
Sqlite.Row => read_first stmt
Sqlite.Done => Sqlite.Err Sqlite.MissingRow
Sqlite.StepError(error) => Sqlite.Err error
}

read_first<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Copied> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
read_first stmt = match Sqlite.column_int (stmt, 0) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(integer) => match Sqlite.column_text (stmt, 1) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(text) => match Sqlite.column_bytes (stmt, 2) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(bytes) => read_empty (stmt, integer, text, bytes)
}
}
}

read_empty<S, C> : (Sqlite.Statement<S, C>, Int, Sqlite.TextOrNull, Sqlite.BytesOrNull) -> Sqlite.Result<Copied> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
read_empty (stmt, integer, text, bytes) = match Sqlite.column_text (stmt, 3) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(empty_text) => match Sqlite.column_bytes (stmt, 4) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(empty_bytes) => read_null (stmt, integer, text, bytes, empty_text, empty_bytes)
}
}

read_null<S, C> : (Sqlite.Statement<S, C>, Int, Sqlite.TextOrNull, Sqlite.BytesOrNull, Sqlite.TextOrNull, Sqlite.BytesOrNull) -> Sqlite.Result<Copied> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
read_null (stmt, integer, text, bytes, empty_text, empty_bytes) = match Sqlite.column_text (stmt, 5) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(null_text) => match Sqlite.column_bytes (stmt, 6) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(null_bytes) => match Sqlite.column_text (stmt, 7) {
Sqlite.Err(error) => Sqlite.Err error
Sqlite.Ok(nul_text) => finish_copy (stmt, Copied(integer, text, bytes, empty_text, empty_bytes, null_text, null_bytes, nul_text))
}
}
}

finish_copy<S, C> : (Sqlite.Statement<S, C>, Copied) -> Sqlite.Result<Copied> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
finish_copy (stmt, value) = {
let copied : Unit -> Copied = fn(ignored) {
value
}
match Sqlite.step stmt {
Sqlite.Done => Sqlite.Ok (copied ())
Sqlite.Row => Sqlite.Err Sqlite.UnexpectedRow
Sqlite.StepError(error) => Sqlite.Err error
}
}
