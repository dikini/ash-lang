pub syntax check $value:expr => {
    match $value {
        true => 42
        false => 0
    }
}

pub syntax tuple_check $value:expr => {
    match $value {
        (true, _) => 42
        (false, _) => 0
    }
}
