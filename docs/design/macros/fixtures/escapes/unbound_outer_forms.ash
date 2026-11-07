pub syntax declaration: (unbound_outer) $name:ident => {
    pub $name : Unit -> Int
    $name () = syntax { $missing }
}
