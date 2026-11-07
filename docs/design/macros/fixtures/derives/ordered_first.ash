import ordering_forms (syntax first_failure, syntax second_failure)

type Color = Red
deriving (first_failure, second_failure)

main : Unit -> Int
main () = 42
