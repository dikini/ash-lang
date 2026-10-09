import @builtin.cell as Cell
import @foreign.sqlite as Native
import provider as Provider
import capture_library as Library

main : Unit -> (Provider.Scope<Native.OpenError, Native.CloseError, (Library.Error, Library.Error)>, Int)
main () = resource cell<O> trace = 0 {
    let result = handle (Library.both ()) with Library.H {
        op ignored => {
            let ignored = Cell.write (trace, (Cell.read trace) + 21)
            resume ()
        }
    }
    (result, Cell.read trace)
}
