effect Outer {
    stop : Unit -> Unit
}
effect Inner {
    report : Unit -> Unit
}
main : Unit -> Unit
main () = handle (handle (cleanup fn(ignored) {
    perform Inner.report ()
} {
    let passed = handle (perform Inner.report ()) with Inner {
        report ignored => resume ()
    }
    perform Outer.stop ()
}) with Outer {
    stop ignored => discard
}) with Inner {
    report ignored => resume ()
}
