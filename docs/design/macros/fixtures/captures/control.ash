pub forty_two : Unit -> Int
forty_two () = 40 + 2

pub selected : Bool -> Int
selected true = 42
selected _ = 0

passed : Unit -> Int
passed () = 42

pub first : Unit -> Int
first () = 1
pub second : Unit -> Int
second () = 1

main : Unit -> Int
main () = forty_two(()) + selected(true) + passed(()) + first(()) + second(())
