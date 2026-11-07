import api as Owner

pub syntax verify $path:ident with $value:expr => {
    newtype Token = Token(Unit)
    with $path.Check<Token> {
        check ignored = 2
    }
    $path.check(Token(())) + $value
}

pub syntax verify_owner $name:ident with $value:expr => {
    newtype Token = Token(Unit)
    with Owner.$name<Token> {
        check ignored = 2
    }
    Owner.check(Token(())) + $value
}
