main : Unit -> Int
main () = {
    let rec first : Unit -> Int = fn(ignored) {
        second ()
    }
    and second : Unit -> Int = fn(ignored) {
        let saved : Unit -> Int = fn(value) {
            first value
        }
        42
    }
    first ()
}
