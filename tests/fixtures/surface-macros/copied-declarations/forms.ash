pub syntax duplicate $value:expr => {
    $value + $value
}

pub syntax plus_one $value:expr => {
    $value + 1
}

outside : Unit -> Int
outside () = 100
