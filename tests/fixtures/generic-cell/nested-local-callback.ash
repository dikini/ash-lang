import @builtin.generic_cell as Cell

relay<R> : ((Cell.Cell<R, Int> -> Unit ! {Cell.Ops<R, Int>}), Cell.Cell<R, Int>) -> Int ! {Cell.Ops<R, Int>} where Cell.Provider<R, Int>
relay (action, value) = {
    let _ = action value
    Cell.read value
}

read_outer<R> : Cell.Cell<R, Int> -> Int ! {Cell.Ops<R, Int>} where Cell.Provider<R, Int>
read_outer outer = resource Cell.Cell<C, Int> local = 41 {
    let write : Cell.Cell<C, Int> -> Unit ! {Cell.Ops<C, Int>} = fn(value) {
        Cell.write (value, 42)
    }
    let result = relay (write, local)
    let _ = Cell.read outer
    result
}

main : Unit -> Int
main () = resource Cell.Cell<R, Int> outer = 0 {
    read_outer outer
}
