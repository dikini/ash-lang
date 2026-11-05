import forms (syntax duplicate)
import @builtin.cell as Cell

main : Unit -> Int
main () = duplicate (resource cell<R> c = 21 {
    Cell.read c
})
