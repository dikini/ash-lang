import api (Marker, mark)
import forms (syntax make_value, syntax use_private)
import derives (syntax marker)

type Color = Red
    | Blue
    deriving (marker)

make_value first
make_value second
use_private owner_result

helper : Unit -> Int
helper () = 0

private_calculation : Unit -> Int
private_calculation () = 0

renamed : Unit -> Int
renamed () = 0

pub checked : Unit -> Int
checked () = match mark(Red) {
    true => first(()) + second(()) + owner_result(())
    false => 0
}
