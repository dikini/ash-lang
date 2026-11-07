zero : Unit -> Int
zero () = 100
one : Unit -> Int
one () = 1
two : Unit -> Int
two () = 2
three : Unit -> Int
three () = 3
four : Unit -> Int
four () = 4
five : Unit -> Int
five () = 5

main : Unit -> Int
main () = zero(()) + one(()) * 10 + two(()) * 100 + three(()) * 1000 + four(()) * 10000 + five(()) * 100000
