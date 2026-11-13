first : Unit -> Int
first () = 4 + 1

second : Unit -> Int
second () = 5 + 1

zero : Unit -> Int
zero () = 0 * 10 + 0

one : Unit -> Int
one () = 1 * 10 + 1

two : Unit -> Int
two () = 2 * 10 + 2

main : Unit -> Int
main () = first(()) + second(()) + zero(()) + one(()) + two(())
