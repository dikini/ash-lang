import syntax_generated_outer (syntax generated_fresh)

bump : Int -> Int
bump value = value + 100

main : Unit -> Int
main () = generated_fresh 40
