import @builtin.cell as Cell

read_outer<R> : Cell.Handle<R> -> Int ! {Cell.Ops<R>} where Cell.Provider<R>
read_outer outer = resource cell<C> cursor = 0 {
    handle ({
        let _ = Cell.read cursor
        Cell.read outer
    }) with Cell.Ops<C> {
        read ignored => resume 0
        write ignored => resume ()
    }
}

main : Unit -> Int
main () = resource cell<R> outer = 42 {
    read_outer outer
}
