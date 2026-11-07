import api (Indexed, index)
import derives (syntax indexed)

type Color = Red
    | Blue
    deriving (indexed)

main : Unit -> Int
main () = index(Red) + index(Blue) + 40
