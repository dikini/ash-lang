import @builtin.cell as Cell
import provider as Provider
import callback_library as Library
import @foreign.sqlite as Native

observe : Unit -> Unit ! {Library.J}
observe () = perform Library.J.op ()

main : Unit -> (Provider.Scope<Native.OpenError, Native.CloseError, Library.Error>, Int)
main () = resource cell<O> trace = 0 {
let result = handle (handle (Library.client observe) with Library.H {
op ignored => {
let ignored = Cell.write (trace, (Cell.read trace) + 40)
resume ()
}
}) with Library.J {
op ignored => {
let ignored = Cell.write (trace, (Cell.read trace) + 2)
resume ()
}
}
(result, Cell.read trace)
}
