import api as Owner

pub syntax unused $name:ident in $value:expr => {
    match $value {
        Owner.$name((inner, inner)) => inner
    }
}

main : Unit -> Int
main () = 42
