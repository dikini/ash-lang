import syntax_constructed_ops (syntax bind_fresh)

main : Unit -> Int
main () = {
    let temp = 40
    (bind_fresh 1 in temp) + 1
}
