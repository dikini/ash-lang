import @builtin.foreign as Foreign
import @builtin.cell as Cell
import producer as Producer

initial : Unit -> Int
initial () = 7

main : Unit -> Int
main () = foreign host H {
    resource cell<C> outer = 0 {
        let report = handle {
            resource Producer.Probe<H, R> owner = initial {
                let replacement : Unit -> Int = fn(ignored) {
                    let retained = outer
                    42
                }
                Producer.store (owner, replacement)
            }
        } with Producer.Trace {
            note ignored => resume ()
        }
        match report {
            Foreign.CheckedNotAcquired(_) => 0
            Foreign.CheckedCompleted(_, completion) => match completion {
                Foreign.NativeConsumed(Foreign.FinishOk, _) => 0
                Foreign.NativeConsumed(Foreign.FinishError(callback), _) => callback ()
                Foreign.NativeRetained(callback, _) => callback ()
                Foreign.LocalBoundary(_) => 0
            }
        }
    }
}
