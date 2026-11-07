import api (Check as Measure, check as measure)

pub syntax verify $value:expr => {
    newtype Token = Token(Unit)
    with Measure<Token> {
        measure ignored = 2
    }
    measure(Token(())) + $value
}
