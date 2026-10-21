
pub run : Unit -> Int
run () = resource cell<C> outer = 0 {
    let report = handle (foreign host H {
        resource Probe<H, R> owner = initial {
            let replacement : Unit -> Int = fn(ignored) {
                let retained = outer
                42
            }
            store (owner, replacement)
        }
    }) with Trace {
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
