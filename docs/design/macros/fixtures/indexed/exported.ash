import api (Indexed, index)
import derives (syntax indexed)

type Color = Red
    | Blue
    deriving (indexed)

pub computed : Unit -> Int
computed () = index(Red) + index(Blue) + 40
