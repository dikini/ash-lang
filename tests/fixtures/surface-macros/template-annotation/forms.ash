type Token = Hidden(Int)

pub syntax accept $value:expr => {
    let result : Token = $value
    42
}

pub syntax reveal $value:expr => {
    let result : Token = Hidden($value)
    match result {
        Hidden(value) => value
    }
}

pub syntax local $value:expr => {
    newtype Token = Token(Int)
    let result : Token = Token($value)
    match result {
        Token(value) => value
    }
}
