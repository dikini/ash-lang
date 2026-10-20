import @builtin.generic_cell as Cell
main : Unit -> Int
main () = resource Cell.Cell<R,Int> c = 41 {
    handle (Cell.read c) with Cell.Ops<R,Int> {
        read ignored => resume 99
        write ignored => resume ()
    }
}
