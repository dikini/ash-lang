import @builtin.generic_cell as Cell
independent : Unit -> Int
independent () = 7
main : Unit -> (Int,Int)
main () = resource Cell.Cell<A,Int> a = 1 {
    resource Cell.Cell<B,(Unit -> Int)> b = independent {
        let dependent : Unit -> Int = fn(ignored) {
            let held = a
            42
        }
        let reply = handle (Cell.read b) with Cell.Ops<B,(Unit -> Int)> {
            read ignored => {
                let _ = Cell.write (b,dependent)
                resume independent
            }
            write ignored => resume ()
        }
        let later = Cell.read b
        (reply (), later ())
    }
}
