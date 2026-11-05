import macros (syntax bind as with_value)

main : Unit -> Int
main () = {
    let temp = 10
    with_value item = 5 when 42 in item + temp
}
