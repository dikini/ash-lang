zero_single : Unit -> Int
zero_single () = 0

zero_a : Unit -> Int
zero_a () = 0

zero_b : Unit -> Int
zero_b () = 0

first : Unit -> Int
first () = 1

second : Unit -> Int
second () = 1

third : Unit -> Int
third () = 1

main : Unit -> Int
main () = 39 + zero_single(()) + zero_a(()) + zero_b(()) + first(()) + second(()) + third(())
