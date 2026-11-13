import facade (renamed)

private_calculation : Unit -> Int
private_calculation () = 20

pub syntax declaration: (use_private) $name:ident => {
    pub $name : Unit -> Int
    $name () = private_calculation(()) + renamed(())
}
