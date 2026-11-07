import forms (syntax call)

effect Ask {
    ask : Int -> Int
}

main : Unit -> Int
main () = handle (call Ask in (perform Ask.ask 40)) with Ask {
    ask value => resume (value + 2)
}
