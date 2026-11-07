import other_dsl (syntax choose)

main : Unit -> Int
main () = choose true then 35 else 99
