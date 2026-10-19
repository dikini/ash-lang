import @builtin.generic_cell as Cell
independent : Unit -> Int
independent () = 7
main : Unit -> Int
main () = {
    let saved = resource Cell.Cell<A,(Unit -> Int)> a = independent {
        resource Cell.Cell<B,(Unit -> Int)> b = independent {
            let dependent : Unit -> Int = fn(ignored) {
                let held = b
                42
            }
            handle ({
                let _ = Cell.read b
                Cell.read a
            }) with Cell.Ops<B,(Unit -> Int)> {
                read ignored => resume dependent
                write ignored => resume ()
            }
        }
    }
    saved ()
}
