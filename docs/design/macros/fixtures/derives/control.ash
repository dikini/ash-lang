import api (Marker, mark, Tagged, tag)

type Color = Red
    | Blue

impl Marker<Color> {
    mark _ = true
}

impl Tagged<Color> {
    tag _ = 42
}

newtype Count = Count(Int)

impl Marker<Count> {
    mark _ = true
}

impl Tagged<Count> {
    tag _ = 42
}

main : Unit -> Int
main () = match (mark(Red), mark(Count(0)), tag(Count(0)) == 42) {
    (true, true, true) => tag(Red)
    _ => 0
}
