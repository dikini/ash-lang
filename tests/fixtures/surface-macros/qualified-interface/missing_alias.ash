pub syntax unused $name:ident with $value:expr => {
    with Missing.$name<Int> {
        check ignored = $value
    }
    42
}

main : Unit -> Int
main () = 42
