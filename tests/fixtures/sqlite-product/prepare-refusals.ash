import @ffi.sqlite as Sqlite

type Refusals = Refusals(Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Bool>, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Bool>, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Bool>, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Bool>, Sqlite.Error)
main : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Refusals> ! {Sqlite.Initialize}
main () = resource Sqlite.Connection<C> db = Sqlite.InMemory {
    let empty = resource Sqlite.Statement<E, C> stmt = (db, "   ") {
        true
    }
    let multiple = resource Sqlite.Statement<M, C> stmt = (db, "SELECT 1; SELECT 2") {
        true
    }
    let nul = resource Sqlite.Statement<N, C> stmt = (db, "SELECT 1\0") {
        true
    }
    let syntax = resource Sqlite.Statement<F, C> stmt = (db, "SELEC 1") {
        true
    }
    let diagnostic = Sqlite.diagnostic db
    Refusals(empty, multiple, nul, syntax, diagnostic)
}
