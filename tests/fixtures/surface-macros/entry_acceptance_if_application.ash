import acceptance_if_forms (syntax if)
apply : Int -> Int
apply value = value
main : Unit -> Int
main () = apply if true then 42 else 0
