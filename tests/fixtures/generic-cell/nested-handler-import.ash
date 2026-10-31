import @builtin.generic_cell as Scoped

pub read_outer<R> : Scoped.Cell<R, Int> -> Int ! {Scoped.Ops<R, Int>} where Scoped.Provider<R, Int>
read_outer outer = resource Scoped.Cell<C, Int> cursor = 0 {
    handle ({
        let _ = Scoped.read cursor
        Scoped.read outer
    }) with Scoped.Ops<C, Int> {
        read ignored => resume 0
        write ignored => resume ()
    }
}
