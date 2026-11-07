import api (mark)
import opaque_subject (Secret, make, impl Marker)

main : Unit -> Int
main () = match mark(make(())) {
    true => 42
    false => 0
}
