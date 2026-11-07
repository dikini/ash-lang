import owner_generic_forms as Forms
import owner_generic_forms (syntax local)

main : Unit -> Int
main () = perform Forms.Hidden<Int>.ask 42
