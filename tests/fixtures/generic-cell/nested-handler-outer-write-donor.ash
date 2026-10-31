import @builtin.generic_cell as Cell

independent : Unit -> Int
independent () = 7

put<R> : Cell.Cell<R, (Unit -> Int)> -> Unit ! {Cell.Ops<R, (Unit -> Int)>} where Cell.Provider<R, (Unit -> Int)>
put outer = resource Cell.Cell<C, (Unit -> Int)> inner = independent {
    handle ({
        let _ = Cell.read inner
        let candidate : Unit -> Int = fn(ignored) {
            let held = 9999
            42
        }
        Cell.write (outer, candidate)
    }) with Cell.Ops<C, (Unit -> Int)> {
        read ignored => resume independent
        write ignored => resume ()
    }
}

main : Unit -> Int
main () = resource Cell.Cell<A, (Unit -> Int)> outer = independent {
    let _ = put outer
    let saved = Cell.read outer
    saved ()
}
