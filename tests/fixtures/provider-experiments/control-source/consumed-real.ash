import provider as Provider
import sqlite as Sqlite

main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.StepResult>>
main () = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {
    resource Sqlite.Statement<S> stmt = (db, (Sqlite.failing_query ())) {
        Sqlite.step stmt
    }
}
