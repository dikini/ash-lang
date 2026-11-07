import forms (syntax duplicate)
import @builtin.cell as Cell
import @builtin.foreign as Foreign

keep_address : Foreign.Address -> Foreign.Address
keep_address address = address

main : Unit -> Int
main () = duplicate (resource cell<R> c = 21 {
    Cell.read c
})
