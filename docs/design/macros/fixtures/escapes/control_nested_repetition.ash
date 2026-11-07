first : Unit -> Int
first () = 10 + 0

second : Unit -> Int
second () = 20 + 1

third : Unit -> Int
third () = 30 + 2

fourth : Unit -> Int
fourth () = 40 + 3

main : Unit -> Int
main () = first(()) + second(()) * 10 + third(()) * 100 + fourth(()) * 1000
