pub interface Read<A> {
    read : A -> Int
}

impl Read<Int> {
    read value = value + 100
}

pub syntax measure $value:expr => {
    read($value)
}
