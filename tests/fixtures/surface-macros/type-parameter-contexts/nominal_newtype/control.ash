newtype Box<A> = Box(A)
main : Unit -> Int
main () = match Box(42) {
    Box(value) => value
}
