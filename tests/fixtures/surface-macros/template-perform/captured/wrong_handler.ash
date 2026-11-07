import forms (syntax request)

effect Ask {
    ask : Int -> Int
}

effect Other {
    ask : Int -> Int
}

main : Unit -> Int
main () = handle (request Ask from 40) with Other {
    ask value => resume value
}
