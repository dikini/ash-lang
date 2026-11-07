pub syntax if $condition:expr then $yes:expr else $no:expr => {
    match $condition {
        true => $yes
        false => $no
    }
}
