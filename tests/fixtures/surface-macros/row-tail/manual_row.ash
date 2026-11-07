interface Run<Key : Type, Rows : EffectRow> {
    run : (Key, Unit -> Int ! {| Rows}) -> Int ! {| Rows}
}

effect Ask {
    ask : Int -> Int
}

invoke<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {| R}
invoke callback = {
    newtype Token = Token(Unit)
    with Run<Token, {| R}> {
        run (token, continuation) = continuation ()
    }
    let action : Unit -> Int ! {| R} = fn(ignored) {
        callback ()
    }
    run (Token(()), action)
}

ask : Unit -> Int ! {Ask}
ask () = perform Ask.ask 40

main : Unit -> Int
main () = handle (invoke ask) with Ask {
    ask value => resume (value + 2)
}
