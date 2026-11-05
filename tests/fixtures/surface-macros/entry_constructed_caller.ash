import syntax_constructed_ops (syntax bind_caller)

main : Unit -> Int
main () = (bind_caller 20 in item) + 2
