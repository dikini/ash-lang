import api (Ask as Alias)

main : Unit -> Int
main () = perform Alias<Int>.ask 42
