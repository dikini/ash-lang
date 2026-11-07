import outer (syntax outer_type)

type MissingType = MissingType(Int)

main : Unit -> Int
main () = outer_type (MissingType(42))
