import syntax_binder_ops (syntax bind_id)

main : Unit -> Int
main () = {
    let item = 40
    let temp = 1
    (bind_id item = item in item + temp) + 1
}
