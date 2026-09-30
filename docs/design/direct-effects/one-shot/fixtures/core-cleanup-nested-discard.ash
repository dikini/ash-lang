import @builtin.cell as Cell
effect Stop {
    stop : Unit -> Unit
}
main : Unit -> Int
main () = resource cell<T> trace = 0 {
    let result = handle (resource cell<A> outer = 1 {
        cleanup fn(ignored) {
            Cell.write (trace, (Cell.read trace) * 10 + Cell.read outer)
        } {
            resource cell<B> inner = 2 {
                cleanup fn(ignored) {
                    Cell.write (trace, (Cell.read trace) * 10 + Cell.read inner)
                } {
                    let stopped = perform Stop.stop ()
                    let suffix = Cell.write (trace, (Cell.read trace) * 10 + 4)
                    42
                }
            }
        }
    }) with Stop {
        stop ignored => {
            let consumed = discard
            let suffix = Cell.write (trace, (Cell.read trace) * 10 + 3)
            7
        }
    }
    result * 10000 + Cell.read trace
}
