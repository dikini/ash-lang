import ordering_forms (syntax first_failure, syntax second_failure)

type Color = Red
deriving (second_failure, first_failure)

main : Unit -> Int
main () = 42
