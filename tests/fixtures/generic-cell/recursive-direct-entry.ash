import @builtin.generic_cell as Cell
visit : (Bool, Unit -> Int) -> Int
visit (again, initial) = resource Cell.Cell<R, (Unit -> Int)> c = initial {
    match again {
        true => {
            let next : Unit -> Int = fn(ignored) {
                let held = c
                9
            }
            visit (false, next)
        }
        false => {
            let saved = Cell.read c
            saved ()
        }
    }
}
initial : Unit -> Int
initial () = 7
main : Unit -> Int
main () = visit (true, initial)
