import api (Indexed, index)
import derives (syntax indexed)

type Color = Red(Int)
    | Blue
    deriving (indexed)

main : Unit -> Int
main () = 42
