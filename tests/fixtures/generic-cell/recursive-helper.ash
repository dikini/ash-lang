import @builtin.generic_cell as Cell
pub visit : (Bool,(Unit -> Int)) -> Int
visit (again,previous) = resource Cell.Cell<R,(Unit -> Int)> c = previous {
    match again {
        true => {
            let next : Unit -> Int = fn(ignored) {
                let held = c
                9
            }
            visit (false,next)
        }
        false => {
            let current = Cell.read c
            current ()
        }
    }
}
