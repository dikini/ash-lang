import types as T

pub syntax accept $value:expr => {
    let result : T.Secret = $value
    42
}
