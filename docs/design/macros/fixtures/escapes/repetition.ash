import forms (syntax zip_values, syntax cached, syntax empty)

zip_values names first, second values 4, 5
cached zero, one, two
empty

main : Unit -> Int
main () = first(()) + second(()) + zero(()) + one(()) + two(())
