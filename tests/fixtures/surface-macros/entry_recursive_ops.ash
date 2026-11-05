import syntax_recursive_ops (syntax make_recursive)

main : Unit -> Int
main () = {
    let item = 100
    let result = make_recursive item = (fn(value) {
        match value == 0 {
            true => 42
            false => item 0
        }
    }) in (item 1)
    match item == 100 {
        true => result
        false => 0
    }
}
