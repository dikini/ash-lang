import forms (syntax make_impl)

interface Marker<A> {
    mark : A -> Bool
}

type Color = Red

make_impl Marker for Color method mark

main : Unit -> Int
main () = match mark(Red) {
    true => 42
    false => 0
}
