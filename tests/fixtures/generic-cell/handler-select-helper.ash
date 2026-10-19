import @builtin.generic_cell as Cell
pub select<A,B> : (Cell.Cell<A,(Unit -> Int)>, Cell.Cell<B,(Unit -> Int)>) -> (Unit -> Int) ! {Cell.Ops<A,(Unit -> Int)>} where Cell.Provider<A,(Unit -> Int)>, Cell.Provider<B,(Unit -> Int)>
select (a,b) = {
    let dependent : Unit -> Int = fn(ignored) {
        let held = b
        42
    }
    handle ({
        let _ = Cell.read b
        Cell.read a
    }) with Cell.Ops<B,(Unit -> Int)> {
        read ignored => resume dependent
        write ignored => resume ()
    }
}
