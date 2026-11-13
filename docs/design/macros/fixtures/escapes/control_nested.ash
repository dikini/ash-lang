first : Unit -> Int
first () = (10 + 1) * 2

second : Unit -> Int
second () = (10 + 1) * 2

main : Unit -> Int
main () = first(()) + second(())
