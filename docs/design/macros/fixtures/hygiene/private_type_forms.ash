pub syntax declaration: (private_type) $name:ident => {
    type Hidden = Hidden

    pub $name : Unit -> Int
    $name () = match Hidden {
        Hidden => 42
    }
}
