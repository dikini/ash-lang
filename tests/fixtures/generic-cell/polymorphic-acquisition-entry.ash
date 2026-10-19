import @builtin.generic_cell as Cell
import @builtin.cell as Legacy

scope<T> : T -> T
scope initial = resource Cell.Cell<C,T> c = initial {
    Cell.read c
}

old<R> : Legacy.Handle<R> -> Int ! {Legacy.Ops<R>} where Legacy.Provider<R>
old value = Legacy.read value

main : Unit -> Int
main () = resource cell<L> legacy = 7 {
    let first = scope (old legacy)
    let second = scope true
    match second {
        true => first
        false => 0
    }
}
