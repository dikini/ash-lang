import @builtin.generic_cell as Cell
import helper (put)
independent : Unit -> Int
independent () = 7
main : Unit -> Int
main () = resource Cell.Cell<A,Int> a = 41 {
    resource Cell.Cell<B,(Unit -> Int)> b = independent {
        let safe : Unit -> Int = fn(ignored) {
            let held = a
            42
        }
        let _ = put (b,safe)
        42
    }
}
