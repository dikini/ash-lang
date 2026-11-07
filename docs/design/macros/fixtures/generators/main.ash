import forms (syntax make_constants)

make_constants starting_at 0 names first, second, third

main : Unit -> Int
main () = first(()) + second(()) * 10 + third(()) * 100
