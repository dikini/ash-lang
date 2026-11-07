interface Marker<A> {
    mark : A -> Bool
}

type Color = Red

impl Marker<Color> {
    mark _ = true
}

main : Unit -> Int
main () = match mark(Red) {
    true => 42
    false => 0
}
