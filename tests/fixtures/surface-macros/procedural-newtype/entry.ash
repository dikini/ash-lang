import forms (syntax local)
newtype Token = Token(Bool)
main : Unit -> Int
main () = local (match Token(true) {
    Token(true) => 42
    _ => 0
})
