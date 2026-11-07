import generic_forms (syntax request)

effect Ask<A> {
    ask : A -> A
}

main : Unit -> Int
main () = handle (request Ask from 40) with Ask<Int> {
    ask value => resume (value + 2)
}
