type Token = Hidden(Int)

pub syntax reveal $value:expr => {
    let identity : Token -> Token = fn(value) {
        value
    }
    match identity(Hidden($value)) {
        Hidden(found) => found
    }
}
