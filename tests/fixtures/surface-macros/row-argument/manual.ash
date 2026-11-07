interface Run<Key : Type, Rows : EffectRow> {
    run : (Key, Unit -> Int ! {| Rows}) -> Int ! {| Rows}
}

effect Ask {
    ask : Int -> Int
}

main : Unit -> Int
main () = handle {
    newtype Token = Token(Unit)
    with Run<Token, {Ask}> {
        run (token, callback) = callback ()
    }
    let action : Unit -> Int ! {Ask} = fn(ignored) {
        perform Ask.ask 40
    }
    run (Token(()), action)
} with Ask {
    ask value => resume (value + 2)
}
