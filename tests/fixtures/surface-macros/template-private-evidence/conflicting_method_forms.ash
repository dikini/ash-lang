import api as Owner
import other_api (foo as check)

pub syntax bad $value:expr => {
    newtype Token = Token(Unit)
    with Owner.Check<Token> {
        check ignored = 2
    }
    Owner.check(Token(())) + $value
}
