interface Equal<A> {
    equal : (A, A) -> Bool
}

impl Equal<Int> {
    equal (left, right) = left == right
}

newtype Box<A> = Box(A)

impl<A> Equal<Box<A>> where Equal<A> {
    equal (Box(left), Box(right)) = equal(left, right)
}

main : Unit -> Int
main () = match equal(Box(42), Box(42)) {
    true => 42
    false => 0
}
