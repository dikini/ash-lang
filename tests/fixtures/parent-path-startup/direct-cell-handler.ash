import @builtin.generic_cell as Cell

effect Read {
    value : Unit -> Int
}

main : Unit -> Int
main () = resource Cell.Cell<R, Int> stored = 42 {
    handle (perform Read.value ()) with Read {
        value () => resume (Cell.read stored)
    }
}
