pub left_before : Unit -> Int
left_before () = 0
pub first : Unit -> Int
first () = 1
pub second : Unit -> Int
second () = 2
pub left_after : Unit -> Int
left_after () = 0
pub right_before : Unit -> Int
right_before () = 3
pub third : Unit -> Int
third () = 4
pub fourth : Unit -> Int
fourth () = 5
pub right_after : Unit -> Int
right_after () = 3

main : Unit -> Int
main () = left_before(()) + left_after(()) + first(()) * 10 + second(()) * 100 + right_before(()) * 1000 + right_after(()) * 1000 + third(()) * 10000 + fourth(()) * 100000
