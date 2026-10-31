import @builtin.cell as Cell
import @builtin.generic_cell as Scoped

read_outer<R> : Scoped.Cell<R, Int> -> Int ! {Scoped.Ops<R, Int>} where Scoped.Provider<R, Int>
read_outer outer = resource Scoped.Cell<C, Int> cursor = 0 {
    handle ({
        let _ = Scoped.read cursor
        Scoped.read outer
    }) with Scoped.Ops<C, Int> {
        read ignored => resume 0
        write ignored => resume ()
    }
}

main : Unit -> Int
main () = resource Scoped.Cell<R, Int> outer = 42 {
    read_outer outer
}
