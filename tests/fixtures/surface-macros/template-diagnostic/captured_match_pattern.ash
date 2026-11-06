import forms (syntax identity)
main : Unit -> Int
main () = identity {
    match 42 {
        true => 42
        false => 0
    }
}
