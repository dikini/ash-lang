import api (Marker, mark)
import generic_forms (syntax generic_marker)

newtype Box<A> = Box(A)
    deriving (generic_marker)

main : Unit -> Int
main () = match mark(Box(42)) {
    true => 42
    false => 0
}
