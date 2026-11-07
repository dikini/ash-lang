import forms (syntax make_effect)

make_effect Ask operation ask

main : Unit -> Int
main () = handle (perform Ask.ask ()) with Ask {
    ask _ => resume 42
}
