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

pub syntax rec_bind $name:ident in $body:expr => {
    let rec $name : Int -> Int = fn(value) {
        match value == 0 {
            true => 42
            false => $name 0
        }
    }
    $body
}

pub syntax rec_mixed $name:ident in $body:expr => {
    let rec item : Unit -> Int = fn(ignored) {
        40
    }
    and $name : Unit -> Int = fn(ignored) {
        (item ()) + 2
    }
    $body
}
