pub syntax times_five $value:expr => {
    $value * 5
}

pub syntax combine $left:expr + $right:expr => {
    $left + $right
}

pub syntax keep_integer $value:expr => {
    let result : Int = $value
    result
}
