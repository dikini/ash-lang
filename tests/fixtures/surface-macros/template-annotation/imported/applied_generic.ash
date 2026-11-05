import applied_forms (syntax accept)

accept_other<Package : Type -> Type> : Package<Int> -> Int
accept_other value = accept value

main : Unit -> Int
main () = 42
