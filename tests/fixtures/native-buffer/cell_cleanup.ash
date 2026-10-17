import native_buffer as Buffer
import @builtin.cell as Cell
main : Unit -> Int
main () = resource cell<S> trace = 0 {
    let result = resource Buffer.Buffer<R> b = 1 {
        cleanup fn(ignored) {
            match Buffer.read (b, 0) {
                Buffer.Success(value) => Cell.write (trace, value)
                Buffer.Failure(error) => ()
            }
        } {
            let _ = Buffer.write (b, 0, 42)
            7
        }
    }
    Cell.read trace
}
