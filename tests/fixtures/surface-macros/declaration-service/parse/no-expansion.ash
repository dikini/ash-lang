import forms (syntax parse_discard, syntax boom)

parse_discard {
    unused : Unit -> Int
    unused () = boom 1
}

main : Unit -> Int
main () = 42
