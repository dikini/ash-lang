pub answer : Unit -> Int
answer () = 42

pub type Shade = Bright

pub local_result : Unit -> Int
local_result () = match Bright {
    Bright => answer(())
}
