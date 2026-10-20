import @builtin.generic_cell as Cell
independent : Unit -> Int
independent () = 7
pub intercept<R> : (Cell.Cell<R,(Unit -> Int)>, (Unit -> Int)) -> Unit where Cell.Provider<R,(Unit -> Int)>
intercept (c,replacement) = handle (Cell.write (c,replacement)) with Cell.Ops<R,(Unit -> Int)> {
    read ignored => resume independent
    write ignored => resume ()
}
