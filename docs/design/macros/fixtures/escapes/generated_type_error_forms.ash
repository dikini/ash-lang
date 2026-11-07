pub syntax declaration: (generated_type_error) $name:ident => {
    pub $name : Unit -> Int
    $name () = ${ syntax { true } }
}
