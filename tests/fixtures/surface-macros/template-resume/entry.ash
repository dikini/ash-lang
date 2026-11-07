import forms (syntax proceed)

effect Ask {
    ask : Unit -> Int
}

main : Unit -> Int
main () = handle (perform Ask.ask ()) with Ask {
    ask ignored => proceed 42
}
