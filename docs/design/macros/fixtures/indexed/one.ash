import api (Indexed, index)
import derives (syntax indexed)

type Color = Red
    deriving (indexed)

main : Unit -> Int
main () = index(Red) + 41
