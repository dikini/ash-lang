import syntax_constructed_ops (syntax use_private)

private_increment : Int -> Int
private_increment value = value + 100

main : Unit -> Int
main () = use_private 41
