import api as Caller

main : Unit -> Int
main () = {
    newtype Token = Token(Unit)
    with Caller.Check<Token> {
        check ignored = 2
    }
    Caller.check(Token(())) + 40
}
