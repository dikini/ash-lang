
pub run : Unit -> Foreign.CheckedScope<Unit, Unit, Unit -> Int>
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
    report
}
