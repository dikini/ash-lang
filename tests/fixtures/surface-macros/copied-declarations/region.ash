import forms (syntax duplicate)

main : Unit -> Int
main () = {
    let outside = 20
    duplicate (region<R> owner {
        using owner {
            outside + 1
        }
    })
}
