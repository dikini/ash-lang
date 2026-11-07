pub syntax declaration: (bad_type) $name:ident => {
    pub $name : Unit -> Int
    $name () = true
}

pub syntax declaration: (need_name) $name:ident => {
    pub $name : Unit -> Int
    $name () = 42
}
