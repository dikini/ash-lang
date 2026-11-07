import acceptance_if_forms (syntax if)
main : Unit -> Int
main () = (if false then 0 else if true then 20 else 0) + (if true then if true then 22 else 0 else 0)
