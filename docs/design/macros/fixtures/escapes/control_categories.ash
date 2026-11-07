plus : Unit -> Int
plus () = 5 + 100

local : Unit -> Int
local () = 7 + 5

named : Unit -> Int
named () = 42

identity : Int -> Int
identity value = value

choose : Bool -> Int
choose true = 42
choose _ = 0

declared : Unit -> Int
declared () = 42

main : Unit -> Int
main () = plus(()) + local(()) + named(()) + identity(3) + choose(true) + declared(())
