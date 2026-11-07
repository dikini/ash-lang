import forms (syntax request)

effect Ask {
    other : Int -> Int
}

main : Unit -> Int
main () = handle (request Ask from 40) with Ask {
    other value => resume value
}
