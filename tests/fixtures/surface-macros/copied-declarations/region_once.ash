import region_once_forms (syntax once)

main : Unit -> Int
main () = {
    let outside = 20
    (once (region<R> owner {
        using owner {
            outside + 1
        }
    })) + 21
}
