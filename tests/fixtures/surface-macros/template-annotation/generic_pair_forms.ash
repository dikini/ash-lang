pub syntax hold $value:expr => {
    newtype Local<A, B> = Local((A, B))
    let local : Local<Int, Bool> = Local(($value, true))
    match local {
        Local((result, _)) => result
    }
}
