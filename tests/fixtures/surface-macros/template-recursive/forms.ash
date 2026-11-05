pub syntax cycle $answer:expr => {
    let rec first : Int -> Int = fn(value) {
        match value == 0 {
            true => $answer
            false => second 0
        }
    }
    and second : Int -> Int = fn(value) {
        first value
    }
    first 1
}
