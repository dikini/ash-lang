import generic_pair_forms (syntax hold)

type Local<A, B> = Other((A, B))

main : Unit -> Int
main () = hold 42
