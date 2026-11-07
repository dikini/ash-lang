interface Run<Key : Type, Rows : EffectRow> {
    run : (Key, Unit -> Int ! {| Rows}) -> Int ! {| Rows}
}

pub syntax unused $body:expr => {
    newtype Token = Token(Unit)
    with Run<Token, {}> {
        run (token, callback) = callback ()
    }
    42
}

main : Unit -> Int
main () = 42
