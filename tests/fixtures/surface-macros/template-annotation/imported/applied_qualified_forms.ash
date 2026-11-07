import types as T

pub syntax accept $value:expr => {
    let result : T.Boxed<Int> = $value
    42
}
