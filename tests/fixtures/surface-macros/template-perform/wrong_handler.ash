import forms (syntax send)

effect Ask {
    ask : Int -> Int
}

main : Unit -> Int
main () = handle (send 42) with Ask {
    ask value => resume value
}
