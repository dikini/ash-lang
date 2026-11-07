import forms (syntax bind)
main : Unit -> Int
main () = bind Token in (match Token(2) {
    Token(_) => 42
})
