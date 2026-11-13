import procedural_forms (syntax make_constants)

make_constants starting_at 0 names zero, one, two, three, four, five

main : Unit -> Int
main () = zero(()) + one(()) * 10 + two(()) * 100 + three(()) * 1000 + four(()) * 10000 + five(()) * 100000
