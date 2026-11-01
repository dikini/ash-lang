factorial : (Int, Int) -> Int
factorial (n, end) = match n == end {
    true => 1
    false => n * factorial (n + 1, end)
}

main : Unit -> Int
main () = factorial (1, 401)
