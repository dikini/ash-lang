pub newtype Box = Box(Int)

main : Unit -> Int
main () = match Box(42) {
    Box(value) => value
}
