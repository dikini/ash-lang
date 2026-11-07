newtype Secret = Secret(Int)

interface Check<Key> {
    check : (Key, Secret) -> Int
}

pub syntax verify $value:expr => {
    newtype Token = Token(Unit)
    with Check<Token> {
        check (ignored, secret) = match secret {
            Secret(value) => value
        }
    }
    check(Token(()), Secret($value)) + 2
}
