import procedural_forms (syntax mixed_depth)

mixed_depth left_before and left_after { first, second }, right_before and right_after { third, fourth }

main : Unit -> Int
main () = left_before(()) + left_after(()) + first(()) * 10 + second(()) * 100 + right_before(()) * 1000 + right_after(()) * 1000 + third(()) * 10000 + fourth(()) * 100000
