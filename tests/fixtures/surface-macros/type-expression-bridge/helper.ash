pub syntax keep $body:expr => {
    $body
}

pub syntax twice $body:expr => {
    $body + $body
}
