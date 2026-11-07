import api as Owner

interface Run<Key : Type, Rows : EffectRow> {
    run : (Key, Unit -> Int ! {| Rows}) -> Int ! {| Rows}
}

pub syntax call $eff:ident in $body:expr => {
    newtype Token = Token(Unit)
    with Run<Token, {$eff}> {
        run (token, callback) = callback ()
    }
    let action : Unit -> Int ! {$eff} = fn(ignored) {
        $body
    }
    run (Token(()), action)
}

pub syntax call_owner $eff:ident in $body:expr => {
    newtype Token = Token(Unit)
    with Run<Token, {Owner.$eff}> {
        run (token, callback) = callback ()
    }
    let action : Unit -> Int ! {Owner.$eff} = fn(ignored) {
        $body
    }
    run (Token(()), action)
}
