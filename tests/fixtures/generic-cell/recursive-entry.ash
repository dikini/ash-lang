import helper (visit)
initial : Unit -> Int
initial () = 7
main : Unit -> Int
main () = visit (true,initial)
