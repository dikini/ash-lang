import forms (syntax make_type)

make_type Color constructor Red

main : Unit -> Int
main () = match Red(42) {
    Red(value) => value
}
