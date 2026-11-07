import types (Boxed as Package)

pub syntax accept $value:expr => {
    let result : Package<Int> = $value
    42
}
