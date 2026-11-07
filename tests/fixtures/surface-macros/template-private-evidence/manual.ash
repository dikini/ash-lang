interface Check<Key> {
    check : Key -> Int
}

main : Unit -> Int
main () = {
    newtype Token = Token(Unit)
    with Check<Token> {
        check ignored = 2
    }
    check(Token(())) + 40
}
