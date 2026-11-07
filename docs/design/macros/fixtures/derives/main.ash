import api (Marker, mark, Tagged, tag)
import forms (syntax marker, syntax tagged)

type Color = Red
    | Blue
    deriving (marker, tagged)

newtype Count = Count(Int)
    deriving (marker, tagged)

main : Unit -> Int
main () = match (mark(Red), mark(Count(0)), tag(Count(0)) == 42) {
    (true, true, true) => tag(Red)
    _ => 0
}
