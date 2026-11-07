import forms (syntax nested_values)

nested_values left { first = 10, second = 20 }, right { third = 30, fourth = 40 }

main : Unit -> Int
main () = first(()) + second(()) * 10 + third(()) * 100 + fourth(()) * 1000
