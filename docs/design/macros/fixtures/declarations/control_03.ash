pub interface Marker<A> {
    mark : A -> Bool
}

impl Marker<Int> {
    mark _ = true
}

main : Unit -> Int
main () = match mark(0) {
    true => 42
    false => 0
}
