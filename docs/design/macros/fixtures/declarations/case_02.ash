import forms (syntax make_newtype)

make_newtype Box constructor Box

main : Unit -> Int
main () = match Box(42) {
    Box(value) => value
}
