interface Check<A> {
    check : A -> Bool
}
impl Check<Int> {
    check _ = true
}
main : Unit -> Int
main () = match check(0) {
    true => 42
    false => 0
}
