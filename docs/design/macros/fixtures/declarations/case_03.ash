import forms (syntax make_interface)

make_interface Marker method mark

impl Marker<Int> {
    mark _ = true
}

main : Unit -> Int
main () = match mark(0) {
    true => 42
    false => 0
}
