import outer (syntax outer_tuple)

type MissingType = MissingType(Int)

main : Unit -> Int
main () = outer_tuple (1, true)
