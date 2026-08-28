type Bad<A> =
    Bad(A<Int>)

main : Unit -> Bad<Int>
main () = Bad(1)
