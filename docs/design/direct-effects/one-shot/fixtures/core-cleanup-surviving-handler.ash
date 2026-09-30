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
}) with Outer {
    stop ignored => discard
}) with Inner {
    report ignored => resume ()
}
