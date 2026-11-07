pub syntax hold $value:expr => {
    newtype Local<A> = Local(A)
    let local : Local<Int> = Local($value)
    match local {
        Local(result) => result
    }
}
