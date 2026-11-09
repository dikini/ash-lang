import forms (syntax sink)

sink {
    passed : Unit -> Int
    passed () = 42
}

main : Unit -> Int
main () = 42
