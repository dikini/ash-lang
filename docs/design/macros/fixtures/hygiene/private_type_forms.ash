pub syntax declaration: (private_type) $name:ident using $typename:ident constructor $constructor:ident => {
    type $typename = $constructor

    pub $name : Unit -> Int
    $name () = match $constructor {
        $constructor => 42
    }
}
