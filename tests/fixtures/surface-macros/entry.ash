import macros (syntax bind as with_value, syntax twice)

main : Unit -> Int
main () = {
    let temp = 10
    (twice (with_value item = 5 when true in item + temp)) + 6
}
