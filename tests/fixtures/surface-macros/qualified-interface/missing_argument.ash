pub syntax unused $path:ident with $value:expr => {
    with $path.Check<Missing> {
        check ignored = $value
    }
    42
}

main : Unit -> Int
main () = 42
