first : Unit -> Int
first () = 0
second : Unit -> Int
second () = 1
third : Unit -> Int
third () = 2
fourth : Unit -> Int
fourth () = 3
main : Unit -> Int
main () = first(()) + second(()) * 10 + third(()) * 100 + fourth(()) * 1000
