import forms (syntax nested_quote)

nested_quote first
nested_quote second

main : Unit -> Int
main () = first(()) + second(())
