import @builtin.cell as Cell
main : Unit -> Unit
main () = resource cell<R> h = 0 {
    let f : Unit -> Unit = fn(u) {
        let ignored = h
        ()
    }
    f ()
}
