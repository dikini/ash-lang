import api (Marker, mark)
import forms (syntax marker as renamed)

type Color = Red
    deriving (renamed,)

main : Unit -> Int
main () = match mark(Red) {
    true => 42
    false => 0
}
