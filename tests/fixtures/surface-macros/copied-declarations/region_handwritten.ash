main : Unit -> Int
main () = {
    let outside = 20
    (region<R> first {
        using first {
            outside + 1
        }
    }) + (region<S> second {
        using second {
            outside + 1
        }
    })
}
