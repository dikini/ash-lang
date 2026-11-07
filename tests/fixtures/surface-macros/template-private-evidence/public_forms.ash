pub interface Check<Key> {
    check : Key -> Int
}

pub syntax verify $value:expr => {
    newtype Token = Token(Unit)
    with Check<Token> {
        check ignored = 2
    }
    check(Token(())) + $value
}
