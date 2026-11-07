pub syntax branches $left:expr else $right:expr => {
    match true {
        true => $left
        false => $right
    }
}
