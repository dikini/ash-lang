import forms (syntax request)

effect Ask {
    ask : Int -> Int
}

main : Unit -> Int
main () = handle (request Ask from 40) with Ask {
    ask value => resume (value + 2)
}
