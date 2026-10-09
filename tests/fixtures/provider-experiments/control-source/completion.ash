import provider as Provider
import sqlite as Sqlite

main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Int>>
main () = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {
    resource Sqlite.Statement<S> stmt = (db, (Sqlite.select_parameter ())) {
        42
    }
}
