import @builtin.cell as Cell
import provider as Provider
import sqlite as Sqlite

main : Unit -> (Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Int>, Int)
main () = resource cell<O> counter = 0 {
    let result = resource Sqlite.Connection<C> db = ({
        let count = Cell.read counter
        let _ = Cell.write (counter, count + 1)
        Sqlite.memory ()
    }) {
        42
    }
    (result, Cell.read counter)
}
