helper_first : Unit -> Int
helper_first () = 21

first : Unit -> Int
first () = helper_first(()) + helper_first(())

helper_second : Unit -> Int
helper_second () = 21

second : Unit -> Int
second () = helper_second(()) + helper_second(())

helper : Unit -> Int
helper () = 0

main : Unit -> Int
main () = first(()) + second(())
