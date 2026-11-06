import api_nullary (On)

main : Unit -> Int
main () = match (On, On) {
    (On, On) => 42
    _ => 0
}
