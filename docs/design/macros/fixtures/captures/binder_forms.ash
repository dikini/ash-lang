pub syntax declaration: (bind_pattern) $name:ident matching $pattern:pattern yields $body:expr => {
    pub $name : Int -> Int
    $name $pattern = $body
}
