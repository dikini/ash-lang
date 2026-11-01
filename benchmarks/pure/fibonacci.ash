fibonacci : (Int, Int) -> Int
fibonacci (n, end) = match n == end {
    true => 0
    false => match n + 1 == end {
        true => 1
        false => fibonacci (n + 1, end) + fibonacci (n + 2, end)
    }
}

main : Unit -> Int
main () = fibonacci (0, 22)
