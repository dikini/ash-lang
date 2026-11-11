import forms (syntax emit)
interface Equal<A> {
    equal : (A, A) -> Bool
}
impl Equal<Int> {
    equal (left, right) = left == right
}
newtype Box<A> = Box(A)
emit Equal for Box method equal constructor Box
main : Unit -> Int
main () = match equal(Box(42), Box(42)) {
    true => 42
    false => 0
}
