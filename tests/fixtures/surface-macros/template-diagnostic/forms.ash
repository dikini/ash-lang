pub syntax add_boolean $value:expr => {
    $value + true
}

pub syntax add_one $value:expr => {
    $value + 1
}

pub syntax identity $value:expr => {
    $value
}
