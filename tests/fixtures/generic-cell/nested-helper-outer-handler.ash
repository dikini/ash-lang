import @builtin.generic_cell as Scoped

read_outer<R> : Scoped.Cell<R, Int> -> Int where Scoped.Provider<R, Int>
read_outer outer = resource Scoped.Cell<C, Int> cursor = 0 {
    handle ({
        let local = Scoped.read cursor
        let value = Scoped.read outer
        local + value
    }) with Scoped.Ops<R, Int> {
        read ignored => resume 42
        write ignored => resume ()
    }
}

main : Unit -> Int
main () = resource Scoped.Cell<R, Int> outer = 100 {
    read_outer outer
}
