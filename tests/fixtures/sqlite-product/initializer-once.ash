import @builtin.cell as Cell
import @ffi.sqlite as Sqlite

main : Unit -> (Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Int>, Int) ! {Sqlite.Initialize}
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
