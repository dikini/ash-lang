import forms (syntax parse_discard)

parse_discard {
    unused : Unit -> Int
    unused () = true
}

main : Unit -> Int
main () = 42
