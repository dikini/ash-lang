import api as Owner

pub syntax unused $value:expr => {
    perform Owner.Ask.missing $value
}

main : Unit -> Int
main () = 42
