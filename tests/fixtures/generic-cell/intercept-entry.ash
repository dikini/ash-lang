import @builtin.generic_cell as Cell
import helper as Helper
independent : Unit -> Int
independent () = 7
main : Unit -> Int
main () = {
    let saved = resource Cell.Cell<R,(Unit -> Int)> c = independent {
        let dependent : Unit -> Int = fn(ignored) {
            let held = c
            42
        }
        let _ = Helper.intercept (c,dependent)
        Cell.read c
    }
    saved ()
}
