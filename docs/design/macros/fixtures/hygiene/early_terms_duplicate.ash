import early_terms_forms (syntax make_value)

make_value first using helper_first
make_value second using helper_first

helper : Unit -> Int
helper () = 0

main : Unit -> Int
main () = first(()) + second(())
