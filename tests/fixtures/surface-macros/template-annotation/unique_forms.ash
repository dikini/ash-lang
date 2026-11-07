pub syntax hold $value:expr => {
    newtype Local = Local(Int)
    let local : Local = Local($value)
    match local {
        Local(result) => result
    }
}
