pub interface Check<A> {
    left : A -> Bool
    right : A -> Bool
}

impl Check<Int> {
    left _ = true
    right _ = true
}

main : Unit -> Int
main () = match (left(0), right(0)) {
    (true, true) => 42
    _ => 0
}
