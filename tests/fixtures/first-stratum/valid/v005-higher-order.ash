fn apply(operation : Int -> Int) -> Int {
    operation 41
}

main : Unit -> Int
main () = apply (fn(value) {
    value + 1
})
