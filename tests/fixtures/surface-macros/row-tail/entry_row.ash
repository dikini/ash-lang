import forms_row (syntax wrap_row)

effect Ask {
    ask : Int -> Int
}

invoke<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {| R}
invoke callback = wrap_row R in (callback ())

ask : Unit -> Int ! {Ask}
ask () = perform Ask.ask 40

main : Unit -> Int
main () = handle (invoke ask) with Ask {
    ask value => resume (value + 2)
}
