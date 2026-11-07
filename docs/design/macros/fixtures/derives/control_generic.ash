import api (Marker, mark)

newtype Box<A> = Box(A)

impl<A> Marker<Box<A>> {
    mark _ = true
}

main : Unit -> Int
main () = match mark(Box(42)) {
    true => 42
    false => 0
}
