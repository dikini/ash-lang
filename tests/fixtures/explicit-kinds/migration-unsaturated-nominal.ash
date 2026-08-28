type Option<A> =
    None
    | Some(A)

bad : Option -> Int
bad _ = 0

main : Unit -> Int
main () = bad None
