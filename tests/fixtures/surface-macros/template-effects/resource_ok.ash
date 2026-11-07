import @builtin.cell as Cell
import pass (syntax pass)
main : Unit -> Int
main () = resource cell<R> c = 41 {
    (pass (Cell.read c)) + 1
}
