import seeds (starting_number)
import procedural_forms (syntax make_constants)

make_constants starting_at (starting_number ()) names first, second, third

main : Unit -> Int
main () = first(()) + second(()) * 10 + third(()) * 100
