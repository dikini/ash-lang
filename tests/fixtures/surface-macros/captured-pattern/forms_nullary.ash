pub syntax both $name:ident in $value:expr => {
    match $value {
        ($name, $name) => 42
        _ => 0
    }
}
