import acceptance_if_forms (syntax if)
apply : Int -> Int
apply value = value
main : Unit -> Int
main () = apply (if true then 40 else 0 + 1) + 2
