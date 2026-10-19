import @builtin.generic_cell as Cell
import helper (get,put)
independent : Unit -> Int
independent () = 7
main : Unit -> Int
main () = {
    let saved = resource Cell.Cell<A,Int> a = 41 {
        resource Cell.Cell<B,(Unit -> Int)> b = independent {
            let dependent : Unit -> Int = fn(ignored) {
                let held = a
                42
            }
            handle (get b) with Cell.Ops<B,(Unit -> Int)> {
                read ignored => {
                    let _ = put (b,dependent)
                    resume independent
                }
                write ignored => resume ()
            }
        }
    }
    saved ()
}
