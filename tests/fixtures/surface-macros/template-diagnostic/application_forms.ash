pub syntax bad_apply $value:expr => {
    1 $value
}

pub syntax call $callee:expr with $value:expr => {
    $callee $value
}

helper : Int -> Int
helper value = value

pub syntax checked $value:expr => {
    helper $value
}
