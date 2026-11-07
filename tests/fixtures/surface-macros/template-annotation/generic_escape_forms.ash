pub syntax escape $value:expr => {
    newtype Local<A> = Local(A)
    let local : A = $value
    42
}
