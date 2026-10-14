import @ffi.native_buffer as Buffer
import @builtin.cell as Cell
effect Stop {
    stop : Unit -> Unit
}
main : Unit -> Int
main () = resource cell<S> trace = 0 {
    let _ = handle (resource Buffer.Buffer<R> outer = 1 {
        cleanup fn(ignored) {
            match (resource Buffer.Buffer<T> inner = 1 {
                Buffer.length inner + 41
            }) {
                Buffer.Success(value) => Cell.write (trace, value)
                Buffer.Failure(error) => Cell.write (trace, 999)
            }
        } {
            let _ = perform Stop.stop ()
            Cell.write (trace, 888)
        }
    }) with Stop {
        stop ignored => {
            let _ = discard
            Buffer.Success ()
        }
    }
    Cell.read trace
}
