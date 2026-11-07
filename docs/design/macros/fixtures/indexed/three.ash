import api (Indexed, index)
import derives (syntax indexed)

type Color = Red
    | Blue
    | Green
    deriving (indexed)

main : Unit -> Int
main () = index(Red) + index(Blue) + index(Green) + 39
