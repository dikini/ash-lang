import other_dsl (syntax choose)

main : Unit -> Int
main () = choose true then choose false then 1 else 35 else 99
