interface Check<Key> {
    check : Key -> Int
}

pub syntax verify $value:expr => {
    newtype Token = Token(Unit)
    with Check<Token> {
        check ignored = 2
    }
    check(Token(())) + $value
}

pub syntax require_evidence $value:expr => {
    check($value)
}

pub syntax verify_as $method:ident from $value:expr => {
    newtype Token = Token(Unit)
    with Check<Token> {
        $method ignored = 2
    }
    check(Token(())) + $value
}
