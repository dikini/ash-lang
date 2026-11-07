import forms (syntax local)
main : Unit -> Int
main () = {
    let value = local 42
    match Token(0) {
        Token(_) => value
    }
}
