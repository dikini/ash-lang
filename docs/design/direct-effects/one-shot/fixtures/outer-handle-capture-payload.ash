import @builtin.cell as Cell

effect Carry<R> {
    send : Cell.Handle<R> -> Int
}

main : Unit -> Int
main () = resource cell<R> outer = 10 {
    handle (resource cell<S> inner = 20 {
        perform Carry<R>.send outer
    }) with Carry<R> {
        send payload => resume 17
    }
}
