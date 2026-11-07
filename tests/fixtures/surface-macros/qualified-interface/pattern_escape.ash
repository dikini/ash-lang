pub syntax unused $path:ident with $value:expr => {
    with $path.Check<Int> {
        check inside = inside
    }
    inside
}

main : Unit -> Int
main () = 42
