import forms (syntax duplicate)

main : Unit -> Int
main () = duplicate ({
    newtype Local = Local(Int)
    match Local(21) {
        Local(value) => value
    }
})
