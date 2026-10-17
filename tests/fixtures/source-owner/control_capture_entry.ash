import @builtin.cell as Cell
import owner as Owner
import helpers as Library

main : Unit -> (Owner.Scope<Unit, Unit, (Library.Error, Library.Error)>, Int)
main () = resource cell<O> trace = 0 {
    let result = handle (Library.both ()) with Library.H {
        op ignored => {
            let ignored = Cell.write (trace, (Cell.read trace) + 21)
            resume ()
        }
    }
    (result, Cell.read trace)
}
