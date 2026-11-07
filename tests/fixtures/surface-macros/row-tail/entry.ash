import forms (syntax wrap)

effect Ask {
    ask : Int -> Int
}

invoke<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {| R}
invoke callback = wrap R in (callback ())

ask : Unit -> Int ! {Ask}
ask () = perform Ask.ask 40

main : Unit -> Int
main () = handle (invoke ask) with Ask {
    ask value => resume (value + 2)
}
