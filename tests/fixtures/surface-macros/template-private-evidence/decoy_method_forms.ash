import api as Owner

pub interface Decoy<Key> {
    check : Key -> Bool
}

pub syntax verify $value:expr => {
    newtype Token = Token(Unit)
    with Owner.Check<Token> {
        check ignored = 2
    }
    Owner.check(Token(())) + $value
}
