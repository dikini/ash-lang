pub syntax both $left:expr then $right:expr => {
    $left + $right
}

pub syntax twice $value:expr => {
    $value + $value
}
