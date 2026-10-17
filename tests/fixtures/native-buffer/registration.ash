import native_buffer as Buffer
import @builtin.cell as Cell
effect Record {
    digit : Int -> Unit
}
effect Adjust {
    publish : Int -> Int
}
visit : Int -> Unit ! {Record, Adjust}
visit depth = resource cell<R> local = depth {
    let _ = resource Buffer.Buffer<S> b = depth {
        cleanup fn(ignored) {
            perform Record.digit (perform Adjust.publish 0)
        } {
            register Adjust (fn(value) {
                value + depth
            }) {
                cleanup fn(ignored) {
                    let _ = perform Record.digit (Cell.read local + Buffer.length b)
                    perform Record.digit (perform Adjust.publish 0)
                } {
                    ()
                }
            }
        }
    }
    ()
}
main : Unit -> Int
main () = resource cell<T> trace = 0 {
    let _ = handle (hook Adjust {
        visit 1
    }) with Record {
        digit value => {
            let _ = Cell.write (trace, (Cell.read trace) * 10 + value)
            resume ()
        }
    }
    Cell.read trace
}
