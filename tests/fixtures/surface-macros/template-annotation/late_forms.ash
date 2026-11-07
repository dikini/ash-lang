pub syntax late $value:expr => {
    let result : Local = $value
    newtype Local = Local(Int)
    42
}
