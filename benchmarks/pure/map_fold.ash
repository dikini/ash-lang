type List =
    Nil
    | Cons(Int, List)

range_list : (Int, Int) -> List
range_list (n, end) = match n == end {
    true => Nil
    false => Cons(n, range_list (n + 1, end))
}

map : (Int -> Int, List) -> List
map (f, values) = match values {
    Nil => Nil
    Cons(value, rest) => Cons(f value, map (f, rest))
}

fold : ((Int, Int) -> Int, Int, List) -> Int
fold (f, total, values) = match values {
    Nil => total
    Cons(value, rest) => fold (f, f (total, value), rest)
}

main : Unit -> Int
main () = {
    let values = range_list (1, 401)
    let transform : Int -> Int = fn(value) {
        value * value + 3 * value + 7
    }
    let transformed = map (transform, values)
    let add : (Int, Int) -> Int = fn(total, value) {
        total + value
    }
    fold (add, 0, transformed)
}
