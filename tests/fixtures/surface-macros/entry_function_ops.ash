import syntax_function_ops (syntax make_function)

main : Unit -> Int
main () = {
    let item = 100
    let f : Int -> Int = make_function item in (item + 1)
    f 41
}
