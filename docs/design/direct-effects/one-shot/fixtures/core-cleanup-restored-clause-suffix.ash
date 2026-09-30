import @builtin.cell as Cell
effect E {
    request : Bool -> Unit
}
main : Unit -> Int
main () = resource cell<R> h = 0 {
    let handled = handle (cleanup fn(ignored) {
        Cell.write (h, 7)
    } {
        let first = perform E.request true
        let second = perform E.request false
        Cell.write (h, 99)
    }) with E {
        request flag => match flag {
            true => {
                let continued = resume ()
                Cell.write (h, 11)
            }
            false => discard
        }
    }
    Cell.read h
}
