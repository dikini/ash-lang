import forms (syntax verify)

main : Unit -> Int
main () = {
    newtype Token = Token(Unit)
    with Check<Token> {
        check ignored = 2
    }
    42
}
