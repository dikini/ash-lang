import macros (syntax bind as with_value, make_secret)

main : Unit -> Int
main () = {
    let temp = 10
    let ignored = with_value item = 5 when true in item + temp
    match (make_secret(0), true) {
        (_, true) => 1
    }
}
