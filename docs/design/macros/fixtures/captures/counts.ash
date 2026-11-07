import forms (syntax zeroes, syntax ones)

zeroes
zeroes zero_single
zeroes zero_a, zero_b
ones first
ones second, third

main : Unit -> Int
main () = 39 + zero_single(()) + zero_a(()) + zero_b(()) + first(()) + second(()) + third(())
