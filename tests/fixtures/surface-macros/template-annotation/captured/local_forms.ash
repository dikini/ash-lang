pub syntax local $name:ident from $value:expr => {
    newtype $name = $name(Int)
    let result : $name = $name($value)
    42
}
