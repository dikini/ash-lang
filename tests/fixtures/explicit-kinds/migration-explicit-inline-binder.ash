fn identity<A>(value : A) -> A {
    value
}

main : Unit -> Int
main () = identity(42)
