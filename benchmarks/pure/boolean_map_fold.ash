type Flags =
    Nil
    | Cons(Bool, Flags)

append : (Flags, Flags) -> Flags
append (left, right) = match left {
    Nil => right
    Cons(value, rest) => Cons(value, append (rest, right))
}

map : (Bool -> Bool, Flags) -> Flags
map (f, values) = match values {
    Nil => Nil
    Cons(value, rest) => Cons(f value, map (f, rest))
}

fold : ((Bool, Bool) -> Bool, Bool, Flags) -> Bool
fold (f, total, values) = match values {
    Nil => total
    Cons(value, rest) => fold (f, f (total, value), rest)
}

main : Unit -> Bool
main () = {
    let pair = Cons(true, Cons(false, Nil))
    let four = append (pair, pair)
    let eight = append (four, four)
    let sixteen = append (eight, eight)
    let thirty_two = append (sixteen, sixteen)
    let sixty_four = append (thirty_two, thirty_two)
    let one_twenty_eight = append (sixty_four, sixty_four)
    let two_fifty_six = append (one_twenty_eight, one_twenty_eight)
    let tail = append (one_twenty_eight, sixteen)
    let values = append (two_fifty_six, tail)
    let flip : Bool -> Bool = fn(value) {
        match value {
            true => false
            false => true
        }
    }
    let transformed = map (flip, values)
    let xor : (Bool, Bool) -> Bool = fn(total, value) {
        match value {
            false => total
            true => match total {
                true => false
                false => true
            }
        }
    }
    fold (xor, false, transformed)
}
