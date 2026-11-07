import extra_forms (syntax make_methods)

make_methods Check first left second right

impl Check<Int> {
    left _ = true
    right _ = true
}

main : Unit -> Int
main () = match (left(0), right(0)) {
    (true, true) => 42
    _ => 0
}
