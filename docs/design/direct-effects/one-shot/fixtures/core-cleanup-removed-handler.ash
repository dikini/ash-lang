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
    perform Outer.stop ()
}) with Inner {
    report ignored => resume ()
}) with Outer {
    stop ignored => discard
}
