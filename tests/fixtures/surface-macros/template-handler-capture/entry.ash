import forms (syntax listen)

effect Ask {
    ask : Int -> Int
}

main : Unit -> Int
main () = listen Ask for 42
