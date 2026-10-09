import @builtin.cell as Cell

main : Unit -> Int
main () = {
    let later = resource cell<R> outer = 41 {
        resource cell<R> inner = 99 {
            let callback : Unit -> Int = fn(ignored) {
                17
            }
            callback
        }
    }
    later ()
}
