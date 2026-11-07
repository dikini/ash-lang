import macros (syntax twice)

main : Unit -> Int
main () = (twice (twice 10)) + 2
