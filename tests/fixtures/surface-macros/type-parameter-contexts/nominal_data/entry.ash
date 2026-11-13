import forms (syntax emit)
emit Box constructor Box
main : Unit -> Int
main () = match Box(42) {
    Box(value) => value
}
