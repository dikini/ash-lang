import forms (syntax make_constants)

starting_number : Unit -> Int
starting_number () = 0

make_constants starting_at (starting_number ()) names first, second, third

main : Unit -> Int
main () = first(()) + second(()) * 10 + third(()) * 100
