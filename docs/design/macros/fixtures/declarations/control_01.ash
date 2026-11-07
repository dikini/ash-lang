pub type Color = Red(Int)

main : Unit -> Int
main () = match Red(42) {
    Red(value) => value
}
