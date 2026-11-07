pub effect Ask {
    ask : Unit -> Int
}

main : Unit -> Int
main () = handle (perform Ask.ask ()) with Ask {
    ask _ => resume 42
}
