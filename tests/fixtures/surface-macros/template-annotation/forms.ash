type Token = Hidden(Int)

pub syntax accept $value:expr => {
    let result : Token = $value
    42
}
