import alias_api (Check, check as measure, measure as flag)

pub syntax verify $value:expr => {
    newtype Token = Token(Unit)
    with Check<Token> {
        measure ignored = 2
        flag ignored = true
    }
    measure(Token(())) + $value
}
