import syntax_identifier_ops (syntax pick)

main : Unit -> Int
main () = {
    let temp = 40
    (pick temp in 0) + 2
}
