pub syntax unused $eff:ident with $value:expr => {
    perform Missing.$eff.ask $value
}

main : Unit -> Int
main () = 42
