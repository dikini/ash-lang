import @builtin.cell as Cell
import @builtin.generic_cell as Scoped

read_outer<R> : Scoped.Cell<R, Int> -> Int ! {Scoped.Ops<R, Int>} where Scoped.Provider<R, Int>
read_outer outer = resource cell<C> cursor = 0 {
    Scoped.read outer
}

main : Unit -> Int
main () = resource Scoped.Cell<R, Int> outer = 42 {
    read_outer outer
}
