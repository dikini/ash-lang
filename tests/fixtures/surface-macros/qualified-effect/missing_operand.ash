import api as Owner

pub syntax unused $eff:ident with $value:expr => {
    perform Owner.$eff.ask missing
}

main : Unit -> Int
main () = 42
