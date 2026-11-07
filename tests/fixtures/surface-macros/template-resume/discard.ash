import forms (syntax stop)

effect Ask {
    ask : Unit -> Int
}

main : Unit -> Int
main () = handle (perform Ask.ask ()) with Ask {
    ask ignored => {
        let ignored = stop ()
        42
    }
}
