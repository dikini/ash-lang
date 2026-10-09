import @builtin.cell as Cell

effect Send {
    send : (Unit -> Int) -> Unit
}

main : Unit -> Unit
main () = handle (resource cell<R> c = 41 {
    perform Send.send (fn(ignored) {
        let held = c
        42
    })
}) with Send {
    send payload => resume ()
}
