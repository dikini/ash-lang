import @builtin.generic_cell as Cell
main : Unit -> Int
main () = resource Cell.Cell<R,Int> c = 41 {
    let _ = handle (Cell.write (c,42)) with Cell.Ops<R,Int> {
        read value => resume (Cell.read value)
        write pair => {
            let _ = Cell.write pair
            resume ()
        }
    }
    Cell.read c
}
