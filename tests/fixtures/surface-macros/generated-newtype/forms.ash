pub syntax hold $value:expr => {
    newtype Token = Token(Int)
    match Token(1) {
        Token(local) => $value + local
    }
}
