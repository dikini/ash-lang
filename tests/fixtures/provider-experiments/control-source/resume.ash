import provider as Provider
import sqlite as Sqlite

effect Pause {
pause : Unit -> Unit
}
main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Int>>
main () = handle (resource Sqlite.Connection<C> db = (Sqlite.memory ()) {
resource Sqlite.Statement<S> stmt = (db, (Sqlite.select_parameter ())) {
let ignored = perform Pause.pause ()
42
}
}) with Pause {
pause ignored => resume ()
}
