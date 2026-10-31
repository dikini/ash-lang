import @builtin.cell as Legacy
import @builtin.generic_cell as Scoped

pub read_outer<R> : Scoped.Cell<R, Int> -> Int ! {Scoped.Ops<R, Int>} where Scoped.Provider<R, Int>
read_outer outer = resource cell<C> cursor = 0 {
    Scoped.read outer
}
