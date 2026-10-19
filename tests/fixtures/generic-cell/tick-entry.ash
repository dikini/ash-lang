import @builtin.generic_cell as Cell
effect Tick {
    tick : Unit -> Unit
}
main : Unit -> Int
main () = resource Cell.Cell<R,Int> c = 41 {
    let _ = handle (handle (Cell.write (c,42)) with Cell.Ops<R,Int> {
        read ignored => resume 0
        write ignored => {
            let _ = perform Tick.tick ()
            resume ()
        }
    }) with Tick {
        tick ignored => {
            let _ = Cell.write (c,(90 + 9))
            resume ()
        }
    }
    Cell.read c
}
