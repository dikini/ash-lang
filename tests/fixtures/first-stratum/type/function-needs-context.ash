main : Unit -> Int
main () = {
    let identity = {
        fn(value) {
            value
        }
    }
    identity 1
}
