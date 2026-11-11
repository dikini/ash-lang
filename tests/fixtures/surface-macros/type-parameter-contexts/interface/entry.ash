import forms (syntax emit)
emit Check method check
impl Check<Int> {
    check _ = true
}
main : Unit -> Int
main () = match check(0) {
    true => 42
    false => 0
}
