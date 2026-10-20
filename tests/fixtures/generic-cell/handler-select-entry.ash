import @builtin.generic_cell as Cell
import helper as Helper
independent : Unit -> Int
independent () = 7
main : Unit -> Int
main () = {
    let saved = resource Cell.Cell<A,(Unit -> Int)> a = independent {
        resource Cell.Cell<B,(Unit -> Int)> b = independent {
            Helper.select (a,b)
        }
    }
    saved ()
}
