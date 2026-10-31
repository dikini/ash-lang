import @builtin.cell as Cell

read_outer<R> : Cell.Handle<R> -> Int ! {Cell.Ops<R>} where Cell.Provider<R>
read_outer outer = resource cell<C> cursor = 0 {
    Cell.read outer
}

main : Unit -> Int
main () = resource cell<R> outer = 42 {
    read_outer outer
}
