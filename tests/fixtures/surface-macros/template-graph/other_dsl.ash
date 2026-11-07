pub syntax bump $value:expr => {
    $value + 1
}

pub syntax choose $condition:expr then $yes:expr else $no:expr => {
    match $condition {
        true => $yes
        false => $no
    }
}
