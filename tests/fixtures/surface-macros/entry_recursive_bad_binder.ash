import syntax_recursive_ops (syntax bad_recursive)

main : Unit -> Int
main () = bad_recursive 42 then (fn(value) {
    value
})
