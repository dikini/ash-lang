import missing_literal (syntax call)

effect Ask {
    ask : Int -> Int
}

main : Unit -> Int
main () = call Ask in 42
