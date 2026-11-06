pub syntax unused $name:ident in $value:expr => {
    match $value {
        Missing.$name(inner) => inner
    }
}

main : Unit -> Int
main () = 42
