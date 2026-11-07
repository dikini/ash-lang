import outer (syntax outer_tuple)

type MissingType = MissingType(Int)

main : Unit -> Int
main () = outer_tuple (MissingType(42), true)
