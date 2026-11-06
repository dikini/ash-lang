import api as Owner
import api (Check)
import other_api (foo as check)

main : Unit -> Int
main () = {
    newtype Token = Token(Unit)
    with Check<Token> {
        check ignored = 2
    }
    Owner.check(Token(())) + 40
}
