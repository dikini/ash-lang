first : Unit -> Int
first () = 100
second : Unit -> Int
second () = 1
third : Unit -> Int
third () = 2
main : Unit -> Int
main () = first(()) + second(()) * 10 + third(()) * 100
