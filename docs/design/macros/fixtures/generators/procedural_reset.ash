import procedural_forms (syntax reset_groups)

reset_groups left { first, second }, right { third, fourth }

main : Unit -> Int
main () = first(()) + second(()) * 10 + third(()) * 100 + fourth(()) * 1000
