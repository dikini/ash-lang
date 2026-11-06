interface Run<Key : Type, Rows : EffectRow> {
    run : (Key, Unit -> Int ! {| Rows}) -> Int ! {| Rows}
}

pub syntax unused $eff:ident in $body:expr => {
    with Run<Int, {$eff, Missing}> {
        run value = 42
    }
    $body
}

main : Unit -> Int
main () = 42
