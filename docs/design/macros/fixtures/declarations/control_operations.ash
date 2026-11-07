pub effect Ask {
    left : Unit -> Int
    right : Unit -> Int
}

main : Unit -> Int
main () = handle (perform Ask.left ()) with Ask {
    left _ => resume 42
    right _ => resume 0
}
