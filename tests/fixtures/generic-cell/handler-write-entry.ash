import @builtin.generic_cell as Cell
main : Unit -> Int
main () = resource Cell.Cell<R,Int> c = 41 {
    let _ = handle (Cell.write (c,42)) with Cell.Ops<R,Int> {
        read ignored => resume 99
        write ignored => resume ()
    }
    Cell.read c
}
