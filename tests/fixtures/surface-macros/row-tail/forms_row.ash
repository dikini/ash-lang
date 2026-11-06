interface Run<Key : Type, Rows : EffectRow> {
    run : (Key, Unit -> Int ! {| Rows}) -> Int ! {| Rows}
}

pub syntax wrap_row $tail:ident in $body:expr => {
    newtype Token = Token(Unit)
    with Run<Token, {| $tail}> {
        run (token, callback) = callback ()
    }
    let action : Unit -> Int ! {| $tail} = fn(ignored) {
        $body
    }
    run (Token(()), action)
}
