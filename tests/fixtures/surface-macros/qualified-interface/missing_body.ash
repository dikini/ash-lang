pub syntax unused $path:ident with $value:expr => {
    with $path.Check<Int> {
        check ignored = missing
    }
    42
}

main : Unit -> Int
main () = 42
