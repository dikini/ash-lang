import facade (renamed)

private_calculation : Unit -> Int
private_calculation () = 20

pub syntax declaration: (make_value) $name:ident => {
    helper : Unit -> Int
    helper () = 21
    pub $name : Unit -> Int
    $name () = helper(()) + helper(())
}

pub syntax declaration: (use_private) $name:ident => {
    pub $name : Unit -> Int
    $name () = private_calculation(()) + renamed(())
}
