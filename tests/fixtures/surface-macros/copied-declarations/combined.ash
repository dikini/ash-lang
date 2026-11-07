import forms (syntax duplicate, syntax plus_one)
import @builtin.cell as Cell

main : Unit -> Int
main () = {
    let outside = 20
    duplicate ({
        newtype Local = Local(Int)
        resource cell<R> c = outside {
            match Local(plus_one (Cell.read c)) {
                Local(value) => value
            }
        }
    })
}
