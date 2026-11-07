import @builtin.cell as Cell
import pass (syntax pass)
main : Unit -> Int
main () = {
    let escaped : Unit -> Int = resource cell<R> c = 41 {
        let saved : Unit -> Int = fn(ignored) {
            let held = c
            42
        }
        pass saved
    }
    escaped ()
}
