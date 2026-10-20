import @builtin.generic_cell as Cell

main : Unit -> (Int,Int)
main () = resource Cell.Cell<A,Int> side = 0 {
    let answer = resource Cell.Cell<B,Int> target = 41 {
        let _ = Cell.write (({
            let before = Cell.read side
            let _ = Cell.write (side,before * 10 + 1)
            target
            }), ({
            let before = Cell.read side
            let _ = Cell.write (side,before * 10 + 2)
            42
        }))
        Cell.read target
    }
    (answer, Cell.read side)
}
