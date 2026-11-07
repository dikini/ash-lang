import api (Marker, mark)

type Color = Red
    | Blue

impl Marker<Color> {
    mark _ = true
}

helper_first : Unit -> Int
helper_first () = 21
helper_second : Unit -> Int
helper_second () = 21
pub first : Unit -> Int
first () = helper_first(()) + helper_first(())
pub second : Unit -> Int
second () = helper_second(()) + helper_second(())
pub owner_result : Unit -> Int
owner_result () = 20 + 22
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
