import syntax_recursive_ops (syntax make_fresh_recursive)

main : Unit -> Int
main () = {
    let item = 42
    make_fresh_recursive (fn(value) {
        value
    }) in item
}
